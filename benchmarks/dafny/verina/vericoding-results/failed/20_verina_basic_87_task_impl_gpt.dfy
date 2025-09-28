// <vc-preamble>
method FindMinIndexInRange(arr: array<int>, start: int, finish: int) returns (result: int)
    requires 
        start <= finish &&
        finish <= arr.Length &&
        start < arr.Length
    ensures
        start <= result < finish
{
    // impl-start
    assume {:axiom} false;
    result := start;
    // impl-end
}

method Swap(a: array<int>, i: int, j: int)
    requires
        a.Length > 0 &&
        0 <= i < a.Length &&
        0 <= j < a.Length
    modifies a
    ensures
        a.Length == old(a.Length) &&
        (0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == old(a[j])) &&
        (0 <= i < a.Length && 0 <= j < a.Length ==> a[j] == old(a[i])) &&
        forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
    // impl-start
    assume {:axiom} false;
    // impl-end
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive sortedness predicate */
predicate IsSorted(s: seq<int>)
  decreases s
{
  |s| <= 1 || (s[0] <= s[1] && IsSorted(s[1..]))
}

/* helper modified by LLM (iteration 5): insertion into a sorted sequence (pure function) */
function Insert(x: int, t: seq<int>): seq<int>
  decreases |t|
{
  if |t| == 0 then
    [x]
  else if x <= t[0] then
    [x] + t
  else
    [t[0]] + Insert(x, t[1..])
}

/* helper modified by LLM (iteration 5): recursive sequence sort (insertion sort over sequences) */
function SortSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [] else Insert(s[0], SortSeq(s[1..]))
}

/* helper modified by LLM (iteration 5): properties of Insert on sorted sequences */
lemma InsertProps(x: int, t: seq<int>)
  requires IsSorted(t)
  ensures IsSorted(Insert(x, t))
  ensures |Insert(x, t)| == |t| + 1
  ensures multiset(Insert(x, t)) == multiset(t) + multiset([x])
  decreases |t|
{
  if |t| == 0 {
    // Insert(x, []) == [x]
  } else {
    if x <= t[0] {
      assert Insert(x, t) == [x] + t;
      // Sorted because head x <= t[0] and tail t is sorted
      assert ([x] + t)[1..] == t;
    } else {
      // x > t[0]
      if |t| == 1 {
        // Insert(x, [t0]) == [t0, x]
        assert Insert(x, t) == [t[0]] + [x];
        assert ([t[0]] + [x])[1..] == [x];
      } else {
        // |t| >= 2, use IH on tail
        assert IsSorted(t);
        assert IsSorted(t[1..]);
        InsertProps(x, t[1..]);
        // Show head ordering for concatenation
        if x <= t[1] {
          assert Insert(x, t[1..]) == [x] + t[1..];
          assert t[0] < x || t[0] <= x; // from x > t[0]
        } else {
          assert Insert(x, t[1..]) == [t[1]] + Insert(x, t[2..]);
          assert t[0] <= t[1];
        }
        assert ([t[0]] + Insert(x, t[1..]))[1..] == Insert(x, t[1..]);
      }
    }
  }
}

/* helper modified by LLM (iteration 5): properties of SortSeq (sortedness, length, multiset) */
lemma SortSeqProps(s: seq<int>)
  ensures IsSorted(SortSeq(s))
  ensures |SortSeq(s)| == |s|
  ensures multiset(SortSeq(s)) == multiset(s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    SortSeqProps(s[1..]);
    InsertProps(s[0], SortSeq(s[1..]));
  }
}

/* helper modified by LLM (iteration 5): from recursive IsSorted to pairwise nondecreasing order */
lemma SortedImpliesForall(s: seq<int>)
  ensures IsSorted(s) ==> (forall i:int, j:int :: 0 <= i <= j < |s| ==> s[i] <= s[j])
  decreases |s|
{
  if IsSorted(s) {
    if |s| <= 1 {
    } else {
      assert IsSorted(s[1..]);
      SortedImpliesForall(s[1..]);
      forall i:int, j:int
        ensures 0 <= i <= j < |s| ==> s[i] <= s[j]
      {
        if 0 <= i <= j < |s| {
          if i == 0 {
            if j == 0 {
            } else if j == 1 {
              assert s[0] <= s[1];
            } else {
              assert 0 <= 0 <= j - 1 < |s[1..]|;
              assert s[1..][0] <= s[1..][j - 1];
              assert s[1] <= s[j];
              assert s[0] <= s[1];
              assert s[0] <= s[j];
            }
          } else {
            assert 0 <= i - 1 <= j - 1 < |s[1..]|;
            assert s[1..][i - 1] <= s[1..][j - 1];
            assert s[i] <= s[j];
          }
        }
      }
    }
  }
}

/* helper modified by LLM (iteration 5): sequence extensionality by index equality */
lemma SeqEqByIndex(a: seq<int>, b: seq<int>)
  requires |a| == |b|
  requires forall k :: 0 <= k < |a| ==> a[k] == b[k]
  ensures a == b
{}

// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i <= j < result.Length ==> result[i] <= result[j]) &&
        multiset(result[..]) == multiset(a[..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): sort via pure sequence SortSeq, copy to array, and prove postconditions */
  var n := a.Length;
  var s := SortSeq(a[..]);
  // Prove properties of s
  SortSeqProps(a[..]);
  assert |s| == n;

  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == n
    invariant forall k :: 0 <= k < i ==> result[k] == s[k]
    decreases n - i
  {
    result[i] := s[i];
    i := i + 1;
  }
  assert i == n;
  assert |result[..]| == |s|;
  assert forall k :: 0 <= k < |s| ==> result[k] == s[k];
  SeqEqByIndex(result[..], s);
  assert result[..] == s;

  // Sortedness
  SortedImpliesForall(s);
  assert IsSorted(s);
  assert forall i':int, j':int :: 0 <= i' <= j' < result.Length ==> result[i'] <= result[j']
    by {
      forall i':int, j':int | 0 <= i' <= j' < result.Length {
        assert |s| == result.Length;
        assert 0 <= i' <= j' < |s|;
        assert s[i'] <= s[j'];
        assert result[i'] == s[i'];
        assert result[j'] == s[j'];
      }
    }

  // Length
  assert result.Length == a.Length;
  // Permutation
  assert multiset(result[..]) == multiset(s);
  assert multiset(s) == multiset(a[..]);
}

// </vc-code>
