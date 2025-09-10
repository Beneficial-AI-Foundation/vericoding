function prefixProduct(s: seq<nat>, i: nat, mod: nat): nat
  requires mod > 0
  requires i <= |s|
{
    if i == 0 then 1
    else (s[i-1] * prefixProduct(s, i-1, mod)) % mod
}

function prefixProducts(s: seq<nat>, mod: nat): seq<nat>
  requires mod > 0
{
    seq(|s|, i requires 0 <= i < |s| => prefixProduct(s, i+1, mod))
}

predicate allDistinct<T(==)>(s: seq<T>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate noForbiddenProducts(s: seq<nat>, forbidden: seq<nat>, mod: nat)
  requires mod > 0
{
    var products := prefixProducts(s, mod);
    forall i :: 0 <= i < |products| ==> products[i] !in forbidden
}

predicate ValidInput(n: nat, m: nat, forbidden: seq<nat>)
{
    m >= 1 &&
    n >= 0 &&
    |forbidden| == n &&
    (forall i :: 0 <= i < |forbidden| ==> 0 <= forbidden[i] < m) &&
    (forall i, j :: 0 <= i < j < |forbidden| ==> forbidden[i] != forbidden[j])
}

predicate ValidSequence(sequence: seq<nat>, m: nat, forbidden: seq<nat>)
  requires m > 0
{
    (forall i :: 0 <= i < |sequence| ==> 0 <= sequence[i] < m) &&
    allDistinct([1] + prefixProducts(sequence, m)) &&
    noForbiddenProducts(sequence, forbidden, m)
}

// <vc-helpers>
lemma prefixProductMod(s: seq<nat>, i: nat, mod: nat)
  requires mod > 0
  requires i <= |s|
  ensures prefixProduct(s, i, mod) < mod
{
  if i == 0 {
  } else {
    prefixProductMod(s, i-1, mod);
  }
}

lemma prefixProductsLength(s: seq<nat>, mod: nat)
  requires mod > 0
  ensures |prefixProducts(s, mod)| == |s|
{
}

lemma prefixProductsBounds(s: seq<nat>, mod: nat)
  requires mod > 0
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < mod
  ensures forall i :: 0 <= i < |prefixProducts(s, mod)| ==> 0 <= prefixProducts(s, mod)[i] < mod
{
  var products := prefixProducts(s, mod);
  forall i | 0 <= i < |products|
    ensures 0 <= products[i] < mod
  {
    prefixProductMod(s, i+1, mod);
  }
}

lemma emptySequenceValid(m: nat, forbidden: seq<nat>)
  requires m > 0
  ensures ValidSequence([], m, forbidden)
{
  var empty := [];
  var products := prefixProducts(empty, m);
  assert products == [];
  assert [1] + products == [1];
  assert allDistinct([1]);
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, forbidden: seq<nat>) returns (length: nat, sequence: seq<nat>)
  requires ValidInput(n, m, forbidden)
  ensures length == |sequence|
  ensures length >= 0
  ensures m == 1 ==> length == 0 && sequence == []
  ensures m > 1 ==> ValidSequence(sequence, m, forbidden)
  ensures n == 0 && m > 1 ==> length > 0
// </vc-spec>
// <vc-code>
{
  if m == 1 {
    length := 0;
    sequence := [];
    return;
  }
  
  var current: seq<nat> := [];
  var forbidden_set := set x | x in forbidden;
  
  while |current| < m - 1
    invariant |current| <= m - 1
    invariant forall i :: 0 <= i < |current| ==> 0 <= current[i] < m
    invariant allDistinct([1] + prefixProducts(current, m))
    invariant noForbiddenProducts(current, forbidden, m)
  {
    var found := false;
    var candidate := 0;
    
    while candidate < m && !found
      invariant 0 <= candidate <= m
      invariant !found ==> forall x :: 0 <= x < candidate ==> 
        var newSeq := current + [x];
        var newProducts := prefixProducts(newSeq, m);
        !allDistinct([1] + newProducts) || newProducts[|newProducts|-1] in forbidden_set
    {
      var newSeq := current + [candidate];
      var newProducts := prefixProducts(newSeq, m);
      
      if allDistinct([1] + newProducts) && newProducts[|newProducts|-1] !in forbidden_set {
        found := true;
      } else {
        candidate := candidate + 1;
      }
    }
    
    if found {
      current := current + [candidate];
    } else {
      break;
    }
  }
  
  length := |current|;
  sequence := current;
}
// </vc-code>

