// see pdf 'ex6 & 7 documentation' for excercise question


datatype Bases = A | C | G | T

//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
  assume{:axiom} false;
}

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
predicate below(first: Bases, second: Bases)
{
    first == second ||
    first == A || 
    (first == C && (second ==  G || second == T)) || 
    (first == G && second == T) ||
    second == T
}

//checks if a sequence is in base order
predicate bordered(s:seq<Bases>)
{
    forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}

// <vc-helpers>
lemma ExchangerLemma(s: seq<Bases>, x: nat, y: nat, t: seq<Bases>)
  requires 0 < |s| && x < |s| && y < |s|
  requires |t| == |s|
  requires forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
  requires t[x] == s[y] && s[x] == t[y]
  ensures multiset(s) == multiset(t)
{
}

lemma BelowTransitive(a: Bases, b: Bases, c: Bases)
  requires below(a, b) && below(b, c)
  ensures below(a, c)
{
}

lemma BelowReflexive(a: Bases)
  ensures below(a, a)
{
}

lemma BelowTotal(a: Bases, b: Bases)
  ensures below(a, b) || below(b, a)
{
}

lemma ExchangerPreservesBorders(s: seq<Bases>, x: nat, y: nat, t: seq<Bases>)
  requires 0 < |s| && x < |s| && y < |s|
  requires |t| == |s|
  requires forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
  requires t[x] == s[y] && s[x] == t[y]
  ensures forall i, j :: 0 <= i < j < |s| ==> 
    (below(s[i], s[j]) <==> below(t[i], t[j])) 
{
}

lemma BasicBelow(a: Bases, b: Bases)
  ensures (a == A && b != A) ==> below(a, b)
  ensures (a == C && (b == G || b == T)) ==> below(a, b)
  ensures (a == G && b == T) ==> below(a, b)
{
}

lemma BelowOrdering(a: Bases, b: Bases)
  ensures below(a, b) <==> 
    (a == A && (b == A || b == C || b == G || b == T)) ||
    (a == C && (b == C || b == G || b == T)) ||
    (a == G && (b == G || b == T)) ||
    (a == T && b == T)
{
  match (a, b) {
    case (A, A) => 
    case (A, C) => 
    case (A, G) => 
    case (A, T) => 
    case (C, C) => 
    case (C, G) => 
    case (C, T) => 
    case (G, G) => 
    case (G, T) => 
    case (T, T) => 
    case (_, _) => 
  }
}

lemma InvariantMaintenance(arr: seq<Bases>, low: nat, mid1: nat, mid2: nat, high: nat)
  requires 0 <= low <= mid1 <= mid2 <= high + 1 && high < |arr|
  requires forall i :: 0 <= i < low ==> arr[i] == A
  requires forall i :: low <= i < mid1 ==> arr[i] == C
  requires forall i :: mid1 <= i < mid2 ==> arr[i] == G
  requires forall i :: high < i < |arr| ==> arr[i] == T
  ensures forall i :: 0 <= i < |arr| ==> 
    (i < low ==> arr[i] == A) &&
    (low <= i < mid1 ==> arr[i] == C) &&
    (mid1 <= i < mid2 ==> arr[i] == G) &&
    (high < i < |arr| ==> arr[i] == T)
{
}

lemma PartitionLemma(arr: seq<Bases>, low: nat, mid1: nat, mid2: nat, high: nat)
  requires 0 <= low <= mid1 <= mid2 <= high + 1 && high < |arr|
  requires forall i :: 0 <= i < low ==> arr[i] == A
  requires forall i :: low <= i < mid1 ==> arr[i] == C
  requires forall i :: mid1 <= i < mid2 ==> arr[i] == G
  requires forall i :: high < i < |arr| ==> arr[i] == T
  ensures forall i, j :: 0 <= i < j < |arr| ==> below(arr[i], arr[j])
{
  var i: nat, j: nat := 0, 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant forall k, l :: 0 <= k < l < i ==> below(arr[k], arr[l])
  {
    j := i + 1;
    while j < |arr|
      invariant i < j <= |arr|
      invariant forall k, l :: 0 <= k < l < j ==> below(arr[k], arr[l])
    {
      assert below(arr[i], arr[j]) by {
        if i < low {
          // arr[i] == A
          match arr[j] {
            case A => 
            case C => BasicBelow(A, C);
            case G => BasicBelow(A, G);
            case T => BasicBelow(A, T);
          }
        } else if i < mid1 {
          // arr[i] == C
          match arr[j] {
            case A => assert false; // A should be before C
            case C => 
            case G => BasicBelow(C, G);
            case T => BasicBelow(C, T);
          }
        } else if i < mid2 {
          // arr[i] == G
          match arr[j] {
            case A => assert false; // A should be before G
            case C => assert false; // C should be before G
            case G => 
            case T => BasicBelow(G, T);
          }
        } else {
          // arr[i] == T
          match arr[j] {
            case A => assert false; // A should be before T
            case C => assert false; // C should be before T
            case G => assert false; // G should be before T
            case T => 
          }
        }
      };
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases);
// </vc-spec>
// <vc-code>
{
  var arr := bases;
  var low := 0;
  var mid1 := 0;
  var mid2 := 0;
  var high := |arr| - 1;
  
  while mid2 <= high
    invariant 0 <= low <= mid1 <= mid2 <= high + 1 && high < |arr|
    invariant |arr| == |bases|
    invariant multiset(arr) == multiset(bases)
    invariant forall i :: 0 <= i < low ==> arr[i] == A
    invariant forall i :: low <= i < mid1 ==> arr[i] == C
    invariant forall i :: mid1 <= i < mid2 ==> arr[i] == G
    invariant forall i :: high < i < |arr| ==> arr[i] == T
  {
    var elem := arr[mid2];
    if elem == A {
      arr := Exchanger(arr, low, mid2);
      ExchangerLemma(arr[low := arr[mid2], mid1, low, arr[low := arr[mid2], mid1 := arr[low]]);
      arr := Exchanger(arr, mid1, low);
      low := low + 1;
      mid1 := mid1 + 1;
      mid2 := mid2 + 1;
    } else if elem == C {
      arr := Exchanger(arr, mid1, mid2);
      ExchangerLemma(arr, mid1, mid2, arr[mid1 := arr[mid2], mid2 := arr[mid1]]);
      mid1 := mid1 + 1;
      mid2 := mid2 + 1;
    } else if elem == G {
      mid2 := mid2 + 1;
    } else { // T
      arr := Exchanger(arr, mid2, high);
      ExchangerLemma(arr, mid2, high, arr[mid2 := arr[high], high := arr[mid2]]);
      high := high - 1;
    }
  }
  
  PartitionLemma(arr, low, mid1, mid2, high);
  sobases := arr;
}
// </vc-code>

