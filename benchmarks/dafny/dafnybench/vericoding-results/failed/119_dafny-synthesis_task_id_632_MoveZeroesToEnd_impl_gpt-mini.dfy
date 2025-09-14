method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
  assume{:axiom} false;
}

function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == value then 1 else 0) + count(arr[1..], value)
}

// <vc-helpers>
function NonZeros(s: seq<int>): seq<int>
{
  if |s| == 0 then [] else if s[0] == 0 then NonZeros(s[1..]) else [s[0]] + NonZeros(s[1..])
}

function Zeros(k: nat): seq<int>
{
  if k == 0 then [] else [0] + Zeros(k - 1)
}

lemma NonZerosAppend(s: seq<int>, a: int)
  ensures NonZeros(s + [a]) == (if a == 0 then NonZeros(s) else NonZeros(s) + [a])
{
  if |s| > 0 {
    NonZerosAppend(s[1..], a);
  }
}

lemma NonZerosConcat(a: seq<int>, b: seq<int>)
  ensures NonZeros(a + b) == NonZeros(a) + NonZeros(b)
{
  if |a| == 0 {
    // trivial
  } else {
    if a[0] == 0 {
      NonZerosConcat(a[1..], b);
    } else {
      NonZerosConcat(a[1..], b);
    }
  }
}

lemma CountConcat(a: seq<int>, b: seq<int>, v: int)
  ensures count(a + b, v) == count(a, v) + count(b, v)
{
  if |a| > 0 {
    CountConcat(a[1..], b, v);
  }
}

lemma CountZerosSeq(k: nat, v: int)
  ensures count(Zeros(k), v) == (if v == 0 then k else 0)
{
  if k > 0 {
    CountZerosSeq(k - 1, v);
  }
}

lemma CountNonZeros(s: seq<int>, v: int)
  ensures count(NonZeros(s), v) == (if v == 0 then 0 else count(s, v))
{
  if |s| == 0 {
    // trivial
  } else {
    if s[0] == 0 {
      CountNonZeros(s[1..], v);
    } else {
      CountNonZeros(s[1..], v);
    }
  }
}

lemma NonZerosIndex(s: seq<int>, p: nat)
  requires p < |s|
  requires s[p] != 0
  ensures NonZeros(s)[|NonZeros(s[..p])|] == s[p]
  ensures |NonZeros(s[..p])| < |NonZeros(s)|
{
  if |s| == 0 {
    // impossible due to requires
  } else if p == 0 {
    // s[0] != 0
  } else {
    if s[0] == 0 {
      NonZerosIndex(s[1..], p - 1);
    } else {
      NonZerosIndex(s[1..], p - 1);
    }
  }
}

lemma ZerosAppend(k: nat)
  ensures Zeros(k) + [0] == Zeros(k + 1)
{
  if k > 0 {
    ZerosAppend(k - 1);
  }
}

lemma CountZerosPlusNonZeros(s: seq<int>)
  ensures |s| == count(s, 0) + |NonZeros(s)|
{
  if |s| > 0 {
    if s[0] == 0 {
      CountZerosPlusNonZeros(s[1..]);
    } else {
      CountZerosPlusNonZeros(s[1..]);
    }
  }
}

lemma CountNonZerosZeros(s: seq<int>, v: int)
  ensures count(NonZeros(s) + Zeros(|s| - |NonZeros(s)|), v) == count(s, v)
{
  // Use CountConcat, CountNonZeros and CountZerosSeq and CountZerosPlusNonZeros
  Calc:
    {
      count(NonZeros(s) + Zeros(|s| - |NonZeros(s)|), v);
      == { CountConcat(NonZeros(s), Zeros(|s| - |NonZeros(s)|), v) }
      count(NonZeros(s), v) + count(Zeros(|s| - |NonZeros(s)|), v);
      == {
        // apply CountNonZeros and CountZerosSeq
      }
    }
  if v == 0 {
    // count(NonZeros(s),0) == 0 and count(Zeros(...),0) == |s| - |NonZeros(s)|
    // so lhs == |s| - |NonZeros(s)|, and by CountZerosPlusNonZeros rhs == count(s,0)
    reveal CountConcat(NonZeros(s), Zeros(|s| - |NonZeros(s)|), v);
    assert count(NonZeros(s) + Zeros(|s| - |NonZeros(s)|), v) == count(NonZeros(s), v) + count(Zeros(|s| - |NonZeros(s)|), v);
    assert count(NonZeros(s), v) == 0 by { CountNonZeros(s, v); }
    assert count(Zeros(|s| - |NonZeros(s)|), v) == (|s| - |NonZeros(s)|) by { CountZerosSeq(|s| - |NonZeros(s)|, v); }
    assert count(NonZeros(s) + Zeros(|s| - |NonZeros(s)|), v) == |s| - |NonZeros(s)|;
    assert count(s, v) == |s| - |NonZeros(s)| by { CountZerosPlusNonZeros(s); }
  } else {
    // v != 0
    reveal CountConcat(NonZeros(s), Zeros(|s| - |NonZeros(s)|), v);
    assert count(NonZeros(s) + Zeros(|s| - |NonZeros(s)|), v) == count(NonZeros(s), v) + count(Zeros(|s| - |NonZeros(s)|), v);
    assert count(Zeros(|s| - |NonZeros(s)|), v) == 0 by { CountZerosSeq(|s| - |NonZeros(s)|, v); }
    assert count(NonZeros(s), v) == count(s, v) by { CountNonZeros(s, v); }
    assert count(NonZeros(s) + Zeros(|s| - |NonZeros(s)|), v) == count(s, v);
  }
}
// </vc-helpers>

// <vc-spec>
method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    // Same size
    ensures arr.Length == old(arr.Length)
    // Zeros to the right of the first zero
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    // The final array is a permutation of the original one
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    // Relative order of non-zero elements is preserved
    ensures forall n, m /* on old array */:: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l /* on new array */:: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
    //ensures IsOrderPreserved(arr[..], old(arr[..]))
    // Number of zeros is preserved
// </vc-spec>
// <vc-code>
{
  var n := arr.Length;
  ghost var oldSeq := arr[..];
  var i := 0;
  var j := 0;
  // Invariant: arr[..j] == NonZeros(oldSeq[..i]) and j == |NonZeros(oldSeq[..i])|
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= j <= n
    invariant arr[..j] == NonZeros(oldSeq[..i])
    invariant j == |NonZeros(oldSeq[..i])|
  {
    if arr[i] != 0 {
      arr[j] := arr[i];
      j := j + 1;
    }
    i := i + 1;
  }
  // Fill the rest with zeros
  var k := j;
  while k < n
    invariant 0 <= j <= n
    invariant 0 <= k <= n
    invariant arr[..j] == NonZeros(oldSeq)
    invariant arr[j..k] == Zeros(k - j)
  {
    arr[k] := 0;
    k := k + 1;
  }
  // Now arr == NonZeros(oldSeq) + Zeros(n - |NonZeros(oldSeq)|)
  assert j == |NonZeros(oldSeq)|;
  assert arr[..j] == NonZeros(oldSeq);
  assert arr[j..n] == Zeros(n - j);
  assert arr[..] == NonZeros(oldSeq) + Zeros(n - |NonZeros(oldSeq)|);
}
// </vc-code>

