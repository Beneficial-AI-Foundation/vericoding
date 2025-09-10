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
  requires mod > 1
  requires i <= |s|
  requires forall j :: 0 <= j < |s| ==> 0 <= s[j] < mod
  ensures prefixProduct(s, i, mod) < mod
{
  if i == 0 {
    assert prefixProduct(s, i, mod) == 1;
    assert 1 < mod;
  } else {
    prefixProductMod(s, i-1, mod);
    assert prefixProduct(s, i-1, mod) < mod;
    assert s[i-1] < mod;
    assert (s[i-1] * prefixProduct(s, i-1, mod)) % mod < mod;
  }
}

lemma prefixProductsLength(s: seq<nat>, mod: nat)
  requires mod > 0
  ensures |prefixProducts(s, mod)| == |s|
{
}

lemma prefixProductsBounds(s: seq<nat>, mod: nat)
  requires mod > 1
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
  requires m > 1
  ensures ValidSequence([], m, forbidden)
{
  var empty := [];
  var products := prefixProducts(empty, m);
  assert products == [];
  assert [1] + products == [1];
  assert allDistinct([1]);
}

lemma extendSequencePreservesValidness(current: seq<nat>, candidate: nat, m: nat, forbidden: seq<nat>)
  requires m > 1
  requires 0 <= candidate < m
  requires forall i :: 0 <= i < |current| ==> 0 <= current[i] < m
  requires ValidSequence(current, m, forbidden)
  ensures forall i :: 0 <= i < |current + [candidate]| ==> 0 <= (current + [candidate])[i] < m
{
}

lemma extendSequenceValidityPreservation(current: seq<nat>, candidate: nat, m: nat, forbidden: seq<nat>)
  requires m > 1
  requires 0 <= candidate < m
  requires ValidSequence(current, m, forbidden)
  requires forall i :: 0 <= i < |current| ==> 0 <= current[i] < m
  requires var newSeq := current + [candidate];
           var newProducts := prefixProducts(newSeq, m);
           allDistinct([1] + newProducts) && noForbiddenProducts(newSeq, forbidden, m)
  ensures ValidSequence(current + [candidate], m, forbidden)
{
  var newSeq := current + [candidate];
  assert forall i :: 0 <= i < |newSeq| ==> 0 <= newSeq[i] < m;
}

lemma validSequenceDistinctProducts(s: seq<nat>, m: nat, forbidden: seq<nat>)
  requires m > 1
  requires ValidSequence(s, m, forbidden)
  ensures allDistinct([1] + prefixProducts(s, m))
{
}

lemma validSequenceNoForbidden(s: seq<nat>, m: nat, forbidden: seq<nat>)
  requires m > 1
  requires ValidSequence(s, m, forbidden)
  ensures noForbiddenProducts(s, forbidden, m)
{
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
  
  emptySequenceValid(m, forbidden);
  
  while |current| < m - 1
    invariant |current| <= m - 1
    invariant forall i :: 0 <= i < |current| ==> 0 <= current[i] < m
    invariant ValidSequence(current, m, forbidden)
    decreases m - 1 - |current|
  {
    var found := false;
    var candidate := 0;
    
    while candidate < m && !found
      invariant 0 <= candidate <= m
      invariant forall i :: 0 <= i < |current| ==> 0 <= current[i] < m
      invariant ValidSequence(current, m, forbidden)
      invariant !found ==> forall x :: 0 <= x < candidate ==> 
        var newSeq := current + [x];
        var newProducts := prefixProducts(newSeq, m);
        !allDistinct([1] + newProducts) || !noForbiddenProducts(newSeq, forbidden, m)
      decreases if found then 0 else m - candidate
    {
      var newSeq := current + [candidate];
      var newProducts := prefixProducts(newSeq, m);
      
      if allDistinct([1] + newProducts) && noForbiddenProducts(newSeq, forbidden, m) {
        found := true;
      } else {
        candidate := candidate + 1;
      }
    }
    
    if found && candidate < m {
      extendSequenceValidityPreservation(current, candidate, m, forbidden);
      current := current + [candidate];
    } else {
      break;
    }
  }
  
  length := |current|;
  sequence := current;
  
  if n == 0 && m > 1 {
    assert |forbidden| == 0;
    assert forbidden_set == {};
    assert length > 0;
  }
}
// </vc-code>

