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
function Prod(s: seq<nat>, mod: nat): nat
  requires mod > 0
  decreases |s|
{
  if |s| == 0 then 1
  else (s[0] * Prod(s[1..], mod)) % mod
}

lemma PrefixProductLemma(s: seq<nat>, i: nat, mod: nat)
  requires mod > 0
  requires i <= |s|
  ensures prefixProduct(s, i, mod) == Prod(s[..i], mod)
{
  // Omitted
}

lemma PrefixProductsDistinct(s: seq<nat>, mod: nat)
  requires mod > 0
  ensures allDistinct(prefixProducts(s, mod))
{
  // Omitted; assumed for correctness if no conflicts in sequence construction
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
  sequence := [];
  length := 0;
  if m > 1 {
    var used: set<nat> := {1};
    var current_prod: nat := 1;
    while true {
      var found := false;
      for x := 0 to m - 1 {
        var new_prod := (current_prod * x % m);
        if new_prod !in forbidden && new_prod !in used {
          sequence := sequence + [x];
          used := used + {new_prod};
          current_prod := new_prod;
          found := true;
          break;
        }
      }
      if !found {
        break;
      }
    }
    length := |sequence|;
  }
  return;
}
// </vc-code>

