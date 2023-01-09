## $K$-d Tree Formalization using Stainless

### Development Environment

- Stainless 0.9.7
- Scala 3.2.0

---

### Verification

#### Instructions

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

#### Result
<img width="752" alt="image" src="https://user-images.githubusercontent.com/43364891/211338168-f959a69c-73e6-4adc-a0ab-909b7f329fca.png">

---
### Run Example
```bash
# in the repo directory
sbt run
```

---

### Presentation Slide

[<img width="983" alt="image" src="https://user-images.githubusercontent.com/43364891/210485513-eed24716-3a30-43a7-8baf-0c2622336705.png">](https://docs.google.com/presentation/d/1S0h7zZM6XCDGRAgVYgzKi4WCzlz5eBWiLG6wShnYY4c/edit?usp=sharing)

---

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
