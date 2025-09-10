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
lemma PrefixProductMonotonic(s: seq<nat>, i: nat, j: nat, mod: nat)
  requires mod > 0
  requires 0 <= i <= j <= |s|
  ensures prefixProduct(s, i, mod) <= prefixProduct(s, j, mod)
  decreases j - i
{
  if i < j {
    PrefixProductMonotonic(s, i, j-1, mod);
    calc {
      prefixProduct(s, j-1, mod);
      <= prefixProduct(s, j, mod);
    }
  }
}

lemma PrefixProductPreservesDistinctness(s: seq<nat>, mod: nat)
  requires mod > 0
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < mod
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  ensures allDistinct([1] + prefixProducts(s, mod))
{
}

lemma NoForbiddenProductsPreservedByPrefix(s: seq<nat>, forbidden: seq<nat>, mod: nat)
  requires mod > 0
  requires forall i :: 0 <= i < |forbidden| ==> 0 <= forbidden[i] < mod
  requires forall i, j :: 0 <= i < j < |forbidden| ==> forbidden[i] != forbidden[j]
  ensures noForbiddenProducts(s, forbidden, mod) == 
          (forall i :: 0 <= i < |prefixProducts(s, mod)| ==> prefixProducts(s, mod)[i] !in forbidden)
{
}

lemma ProductsDistinctHelper(products: seq<nat>, newProduct: nat)
  requires allDistinct(products)
  requires newProduct !in products
  ensures allDistinct(products + [newProduct])
{
}

lemma UsedSetMaintained(used: set<nat>, candidate: nat, newProduct: nat)
  requires candidate !in used
  requires newProduct !in used
  ensures candidate !in used && newProduct !in used
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
  } else {
    var products: seq<nat> := [1];
    var current: seq<nat> := [];
    var used: set<nat> := {1};
    
    var next: nat := 0;
    
    while next < m && |current| < n
      invariant 0 <= next <= m
      invariant |products| == |current| + 1
      invariant products == [1] + prefixProducts(current, m)
      invariant forall i :: 0 <= i < |products| ==> 0 <= products[i] < m
      invariant allDistinct(products)
      invariant forall i :: 0 <= i < |current| ==> 0 <= current[i] < m
      invariant forall i, j :: 0 <= i < j < |current| ==> current[i] != current[j]
      invariant used == set x | x in products
    {
      var candidate: nat := next;
      next := next + 1;
      
      if candidate < m && candidate !in used {
        var lastProduct := products[|products|-1];
        var newProduct := (lastProduct * candidate) % m;
        
        if newProduct !in forbidden && newProduct !in used {
          current := current + [candidate];
          products := products + [newProduct];
          used := used + {candidate, newProduct};
          ProductsDistinctHelper(products, newProduct);
          next := 0;
        }
      }
    }
    
    length := |current|;
    sequence := current;
  }
}
// </vc-code>

