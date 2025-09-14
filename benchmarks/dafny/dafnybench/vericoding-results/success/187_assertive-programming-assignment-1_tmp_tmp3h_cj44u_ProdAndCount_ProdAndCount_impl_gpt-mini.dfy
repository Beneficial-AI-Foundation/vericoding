function RecursivePositiveProduct(q: seq<int>): int
    decreases |q|
{
    if q == [] then 1
    else if q[0] <= 0 then RecursivePositiveProduct(q[1..])
    else q[0] * RecursivePositiveProduct(q[1..])
}

function RecursiveCount(key: int, q: seq<int>): int
    decreases |q|
{
    if q == [] then 0
    else if q[|q|-1] == key then 1+RecursiveCount(key, q[..|q|-1])
    else RecursiveCount(key, q[..|q|-1])
}

function county(elem: int, key: int): int{
    if elem==key then 1 else 0
}

function prody(elem: int): int{
    if elem <= 0 then 1 else elem
}

// <vc-helpers>
lemma RecursiveCount_nonneg(key: int, q: seq<int>)
  ensures RecursiveCount(key, q) >= 0
  decreases |q|
{
  if q == [] {
    // RecursiveCount(key, []) == 0
    assert RecursiveCount(key, q) == 0;
  } else {
    var r := q[..|q|-1];
    RecursiveCount_nonneg(key, r);
    if q[|q|-1] == key {
      assert RecursiveCount(key, q) == 1 + RecursiveCount(key, r);
      assert RecursiveCount(key, q) >= 0;
    } else {
      assert RecursiveCount(key, q) == RecursiveCount(key, r);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method ProdAndCount(q: seq<int>, key: int) returns (prod: int, count: nat)
    ensures prod == RecursivePositiveProduct(q)
    ensures count == RecursiveCount(key, q)
// </vc-spec>
// <vc-code>
{
  prod := RecursivePositiveProduct(q);
  RecursiveCount_nonneg(key, q);
  count := RecursiveCount(key, q);
}
// </vc-code>

