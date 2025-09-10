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
lemma PrefixProductExtension(s: seq<nat>, next: nat, mod: nat)
  requires mod > 0
  ensures prefixProduct(s + [next], |s| + 1, mod) == (prefixProduct(s, |s|, mod) * next) % mod
{
  calc == {
    prefixProduct(s + [next], |s| + 1, mod);
    { assert |s| + 1 > 0; }
    ((s + [next])[|s|] * prefixProduct(s + [next], |s|, mod)) % mod;
    { assert (s + [next])[|s|] == next; }
    (next * prefixProduct(s + [next], |s|, mod)) % mod;
    { assert forall j :: 0 <= j < |s| ==> (s + [next])[j] == s[j];
      PrefixProductEqual(s, s + [next], |s|, mod); }
    (next * prefixProduct(s, |s|, mod)) % mod;
    (prefixProduct(s, |s|, mod) * next) % mod;
  }
}

lemma PrefixProductEqual(s1: seq<nat>, s2: seq<nat>, i: nat, mod: nat)
  requires mod > 0
  requires i <= |s1|
  requires i <= |s2|
  requires forall j :: 0 <= j < i ==> s1[j] == s2[j]
  ensures prefixProduct(s1, i, mod) == prefixProduct(s2, i, mod)
{
  if i == 0 {
    assert prefixProduct(s1, 0, mod) == 1;
    assert prefixProduct(s2, 0, mod) == 1;
  } else {
    assert s1[i-1] == s2[i-1];
    PrefixProductEqual(s1, s2, i-1, mod);
  }
}

lemma PrefixProductsExtension(s: seq<nat>, next: nat, mod: nat)
  requires mod > 0
  ensures |prefixProducts(s + [next], mod)| == |s| + 1
  ensures forall i :: 0 <= i < |s| ==> prefixProducts(s + [next], mod)[i] == prefixProducts(s, mod)[i]
  ensures prefixProducts(s + [next], mod)[|s|] == (prefixProduct(s, |s|, mod) * next) % mod
{
  var prods1 := prefixProducts(s, mod);
  var prods2 := prefixProducts(s + [next], mod);
  
  assert |prods2| == |s + [next]| == |s| + 1;
  
  forall i | 0 <= i < |s|
    ensures prods2[i] == prods1[i]
  {
    assert prods2[i] == prefixProduct(s + [next], i + 1, mod);
    assert prods1[i] == prefixProduct(s, i + 1, mod);
    PrefixProductEqual(s, s + [next], i + 1, mod);
    assert prods2[i] == prods1[i];
  }
  
  assert prods2[|s|] == prefixProduct(s + [next], |s| + 1, mod);
  PrefixProductExtension(s, next, mod);
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
  
  sequence := [];
  var seen := {1} + set i | 0 <= i < |forbidden| :: forbidden[i];
  var currentProduct := 1;
  
  // Verify initial invariants
  assert |sequence| == 0;
  assert prefixProducts(sequence, m) == [];
  assert seen == {1} + (set i | 0 <= i < 0 :: prefixProducts(sequence, m)[i]) + (set i | 0 <= i < |forbidden| :: forbidden[i]);
  assert |seen| == 1 + |forbidden|;
  assert |forbidden| == n;
  assert n < m; // From ValidInput and m > 1
  assert |seen| == 1 + n < m;
  
  while |sequence| < m - 1
    invariant 0 <= |sequence| < m
    invariant ValidSequence(sequence, m, forbidden)
    invariant seen == {1} + (set i | 0 <= i < |prefixProducts(sequence, m)| :: prefixProducts(sequence, m)[i]) + (set i | 0 <= i < |forbidden| :: forbidden[i])
    invariant currentProduct == prefixProduct(sequence, |sequence|, m)
    invariant currentProduct in seen
    invariant |seen| == 1 + |sequence| + |forbidden|
    invariant |seen| <= m
  {
    var found := false;
    var candidate := 0;
    
    while candidate < m && !found
      invariant 0 <= candidate <= m
      invariant !found ==> forall c :: 0 <= c < candidate ==> (currentProduct * c) % m in seen
    {
      var nextProduct := (currentProduct * candidate) % m;
      if nextProduct !in seen {
        found := true;
        sequence := sequence + [candidate];
        seen := seen + {nextProduct};
        currentProduct := nextProduct;
        
        PrefixProductsExtension(sequence[..|sequence|-1], candidate, m);
        assert prefixProducts(sequence, m)[|sequence|-1] == nextProduct;
      } else {
        candidate := candidate + 1;
      }
    }
    
    if !found {
      break;
    }
  }
  
  length := |sequence|;
}
// </vc-code>

