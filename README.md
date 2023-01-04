## $K$-d Tree Formalization using Stainless

### Development Environment

- Stainless 0.9.7
- Scala 3.2.0

### Verification

Optional but **recommended**: Use nix to run a bash shell that provides the development environment.
```bash
nix develop
```

Verify the proof:
```bash
cd src/main/scala
stainless Ordering.scala ListLemmas.scala NestedForallProofs.scala Modification.scala KDTree.scala OptimalConstruction.scala NNQ.scala --timeout=TIMEOUT
```

`TIMEOUT`: Personally I use 10 seconds in my MBP with Intel i7.

### Result
<img width="709" alt="image" src="https://user-images.githubusercontent.com/43364891/210483093-a931046e-499f-4214-a588-558ba50826d5.png">

### Code Structure

```scala
.
├── KDTree.scala // Definition of k-d tree.
├── ListLemmas.scala // Lemmas related to list.
├── Main.scala
├── Modification.scala // Insertion and erasure.
├── NNQ.scala // Nearest Neighbor Search algorithm for Nearest Neighbor Queries.
├── NestedForallProofs.scala // Lemmas related to nested forall. nested forall example: xs.forall(ik => t.forallKeys(k1 => lessThan(k1, ik)))
├── OptimalConstruction.scala // Optimal Construction of k-d tree.
├── Ordering.scala // Definitions and lemmas related to key ordering.
└── RegionSearch.scala // Region Search algorithm.
```

### Proof Outline
TBA
