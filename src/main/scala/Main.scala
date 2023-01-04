import stainless.lang._

def plus_one(x: BigInt): BigInt = {
  x + 1
} ensuring(_ - 1 == x)

@main def hello: Unit = {}
