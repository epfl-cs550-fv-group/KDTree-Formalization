{
  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.flake-utils.url = github:numtide/flake-utils;

  outputs = { self, nixpkgs, flake-utils, ... } @ inputs: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };
      lib = pkgs.lib;

      stainless-lib = pkgs.stdenv.mkDerivation rec {
        name = "stainless-lib";
        version = "0.9.6";

        nativeBuildInputs = with pkgs; [ unzip ];

        sourceRoot = ".";

        src = builtins.fetchurl {
          # We download the mac version here, but it doesn't really matter - we don't use we given z3.
          url = "https://github.com/epfl-lara/stainless/releases/download/v${version}/stainless-dotty-standalone-${version}-mac.zip";
          sha256 = "sha256:1idaqh0rjlkn84fpbfg4viaiz9rcairm8k5wngwzv42rh8596mib";
        };

        installPhase = ''
          mkdir -p $out/lib/stainless
          cp lib/stainless-dotty-standalone-${version}.jar $out/lib/stainless/stainless.jar
        '';
      };

      stainless = pkgs.writeShellApplication {
        name = "stainless";
        runtimeInputs = with pkgs; [ jdk17 z3 ];
        text = ''
          STAINLESS_JAR="${stainless-lib}/lib/stainless/stainless.jar"
          JAVA_OPTS=''${JAVA_OPTS:-""}
          # shellcheck disable=SC2086
          exec java -cp "$STAINLESS_JAR" $JAVA_OPTS stainless.Main "$@"
        '';
      };
    in
    rec
    {
      devShells.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          jdk17
          sbt
          stainless
          metals
        ];
      };
      # For compat
      devShell = devShells.default;
    });
}
