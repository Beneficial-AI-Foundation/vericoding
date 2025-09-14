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
lemma RCNonNeg(key: int, q: seq<int>)
  ensures 0 <= RecursiveCount(key, q)
  decreases |q|
{
  if q == [] {
  } else if q[|q|-1] == key {
    assert |q| > 0;
    RCNonNeg(key, q[..|q|-1]);
    assert RecursiveCount(key, q) == 1 + RecursiveCount(key, q[..|q|-1]);
  } else {
    assert |q| > 0;
    RCNonNeg(key, q[..|q|-1]);
    assert RecursiveCount(key, q) == RecursiveCount(key, q[..|q|-1]);
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
  RCNonNeg(key, q);
  count := RecursiveCount(key, q) as nat;
}
// </vc-code>

