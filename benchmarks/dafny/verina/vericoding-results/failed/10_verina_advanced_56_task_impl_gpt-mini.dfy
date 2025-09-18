// <vc-preamble>
/* Count how many times a specific value appears in the sequence */
function CountVal(val: int, xs: seq<int>): nat 
    decreases |xs|
{
    if |xs| == 0 then
        0
    else
        var rest := CountVal(val, xs[1..]);
        if xs[0] == val then rest + 1 else rest
}

/* Check whether one sequence is a subsequence of another (preserving relative order) */
predicate IsSubsequence(xs: seq<int>, ys: seq<int>) 
    decreases |xs| + |ys|
{
    if |xs| == 0 then
        true
    else if |ys| == 0 then
        false
    else
        if xs[0] == ys[0] then
            IsSubsequence(xs[1..], ys[1..])
        else
            IsSubsequence(xs, ys[1..])
}

function FilterNonZero(xs: seq<int>): seq<int>
{
    if |xs| == 0 then []
    else if xs[0] != 0 then [xs[0]] + FilterNonZero(xs[1..])
    else FilterNonZero(xs[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): length relation between FilterNonZero and CountVal */
lemma LenFilterNonZero(xs: seq<int>) ensures |FilterNonZero(xs)| + CountVal(0, xs) == |xs| decreases |xs| {
  if |xs| == 0 {
    return;
  }
  var h := xs[0];
  LenFilterNonZero(xs[1..]);
  if h != 0 {
    assert FilterNonZero(xs) == [h] + FilterNonZero(xs[1..]);
    assert |FilterNonZero(xs)| == 1 + |FilterNonZero(xs[1..])|;
    assert CountVal(0, xs) == CountVal(0, xs[1..]);
    assert |FilterNonZero(xs)| + CountVal(0, xs) == 1 + |FilterNonZero(xs[1..])| + CountVal(0, xs[1..]);
    assert 1 + |FilterNonZero(xs[1..])| + CountVal(0, xs[1..]) == 1 + |xs[1..]|;
    assert 1 + |xs[1..]| == |xs|;
  } else {
    assert FilterNonZero(xs) == FilterNonZero(xs[1..]);
    assert |FilterNonZero(xs)| == |FilterNonZero(xs[1..])|;
    assert CountVal(0, xs) == 1 + CountVal(0, xs[1..]);
    assert |FilterNonZero(xs)| + CountVal(0, xs) == |FilterNonZero(xs[1..])| + 1 + CountVal(0, xs[1..]);
    assert |FilterNonZero(xs[1..])| + 1 + CountVal(0, xs[1..]) == |xs[1..]| + 1;
    assert |xs[1..]| + 1 == |xs|;
  }
}

/* helper modified by LLM (iteration 5): prefix relation implies subsequence */
lemma PrefixIsSubsequence(prefix: seq<int>, ys: seq<int>) ensures prefix == ys[..|prefix|] ==> IsSubsequence(prefix, ys) decreases |prefix| {
  if |prefix| == 0 {
    return;
  }
  if prefix != ys[..|prefix|] {
    return;
  }
  // equality of slices gives head equality
  assert prefix[0] == ys[0];
  PrefixIsSubsequence(prefix[1..], ys[1..]);
  assert IsSubsequence(prefix, ys);
}

/* helper modified by LLM (iteration 5): CountVal splits over concatenation */
lemma CountValConcat(a: seq<int>, b: seq<int>) ensures CountVal(0, a + b) == CountVal(0, a) + CountVal(0, b) decreases |a| + |b| {
  if |a| == 0 {
    return;
  }
  var h := a[0];
  CountValConcat(a[1..], b);
  if h == 0 {
    assert CountVal(0, a + b) == 1 + CountVal(0, a[1..] + b);
    assert CountVal(0, a) == 1 + CountVal(0, a[1..]);
    assert CountVal(0, a[1..] + b) == CountVal(0, a[1..]) + CountVal(0, b);
    assert CountVal(0, a + b) == CountVal(0, a) + CountVal(0, b);
  } else {
    assert CountVal(0, a + b) == CountVal(0, a[1..] + b);
    assert CountVal(0, a) == CountVal(0, a[1..]);
    assert CountVal(0, a[1..] + b) == CountVal(0, a[1..]) + CountVal(0, b);
    assert CountVal(0, a + b) == CountVal(0, a) + CountVal(0, b);
  }
}

/* helper modified by LLM (iteration 5): CountVal is zero for sequences without zeros */
lemma CountValOfNonZeroSeq(s: seq<int>) ensures (forall t :: 0 <= t < |s| ==> s[t] != 0) ==> CountVal(0, s) == 0 decreases |s| {
  if |s| == 0 {
    return;
  }
  if !(forall t :: 0 <= t < |s| ==> s[t] != 0) {
    return;
  }
  // head is non-zero by the antecedent
  CountValOfNonZeroSeq(s[1..]);
  assert s[0] != 0;
  assert CountVal(0, s) == CountVal(0, s[1..]);
  assert CountVal(0, s[1..]) == 0;
}

/* helper modified by LLM (iteration 5): CountVal equals length for all-zero sequences */
lemma CountValZeros(s: seq<int>) ensures (forall t :: 0 <= t < |s| ==> s[t] == 0) ==> CountVal(0, s) == |s| decreases |s| {
  if |s| == 0 {
    return;
  }
  if !(forall t :: 0 <= t < |s| ==> s[t] == 0) {
    return;
  }
  CountValZeros(s[1..]);
  assert s[0] == 0;
  assert CountVal(0, s) == 1 + CountVal(0, s[1..]);
  assert 1 + CountVal(0, s[1..]) == 1 + |s[1..]|;
  assert 1 + |s[1..]| == |s|;
}

/* helper modified by LLM (iteration 5): FilterNonZero produces only non-zero elements */
lemma FilterNonZeroHasNoZeros(s: seq<int>) ensures forall t :: 0 <= t < |FilterNonZero(s)| ==> FilterNonZero(s)[t] != 0 decreases |s| {
  if |s| == 0 {
    return;
  }
  var h := s[0];
  FilterNonZeroHasNoZeros(s[1..]);
  if h != 0 {
    // FilterNonZero(s) == [h] + FilterNonZero(s[1..])
    assert FilterNonZero(s) == [h] + FilterNonZero(s[1..]);
    // head is non-zero
    assert FilterNonZero(s)[0] == h && h != 0;
    // tail elements are non-zero by induction
    var tail := FilterNonZero(s[1..]);
    assert forall t :: 0 <= t < |tail| ==> tail[t] != 0;
  } else {
    assert FilterNonZero(s) == FilterNonZero(s[1..]);
    // inherited property
    assert forall t :: 0 <= t < |FilterNonZero(s)| ==> FilterNonZero(s)[t] != 0;
  }
}

// </vc-helpers>

// <vc-spec>
method MoveZeroes(xs: array<int>) returns (result: array<int>)
    ensures
        /* All non-zero elements must maintain their relative order */
        IsSubsequence(FilterNonZero(xs[0..xs.Length]), result[0..result.Length])
        /* All zeroes must be located at the end of the output array */
        && (forall i :: 0 <= i < result.Length && result[i] != 0 ==> 
            forall j :: i < j < result.Length ==> result[j] != 0)
        /* The output must contain the same number of elements */
        && xs.Length == result.Length
        /* The number of zeroes must remain unchanged */
        && CountVal(0, xs[0..xs.Length]) == CountVal(0, result[0..result.Length])
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fix ghost assignment to not redeclare */
  var n := xs.Length;
  result := new int[n];
  var i := 0;
  var k := 0;
  ghost var built: seq<int> := [];
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= k <= n
    invariant built == FilterNonZero(xs[0..i])
    invariant forall t :: 0 <= t < k ==> result[t] == built[t]
  {
    if xs[i] != 0 {
      result[k] := xs[i];
      built := built + [xs[i]];
      k := k + 1;
    }
    i := i + 1;
  }

  while k < n
    invariant |built| <= k <= n
    invariant forall t :: 0 <= t < |built| ==> result[t] == built[t]
    invariant forall t :: |built| <= t < k ==> result[t] == 0
  {
    result[k] := 0;
    k := k + 1;
  }

  // Postconditions proofs
  assert built == FilterNonZero(xs[0..n]);
  assert forall t :: 0 <= t < |built| ==> result[t] == built[t];
  assert built == result[0..|built|];
  PrefixIsSubsequence(built, result[0..n]);
  assert IsSubsequence(FilterNonZero(xs[0..n]), result[0..n]);

  LenFilterNonZero(xs[0..n]);
  assert |built| + CountVal(0, xs[0..n]) == n;

  CountValConcat(result[0..|built|], result[|built|..n]);
  assert CountVal(0, result[0..n]) == CountVal(0, result[0..|built|]) + CountVal(0, result[|built|..n]);

  // first part contains no zeros
  FilterNonZeroHasNoZeros(xs[0..n]);
  assert forall t :: 0 <= t < |built| ==> built[t] != 0;
  assert forall t :: 0 <= t < |built| ==> result[t] == built[t];
  assert forall t :: 0 <= t < |built| ==> result[t] != 0;
  CountValOfNonZeroSeq(result[0..|built|]);
  assert CountVal(0, result[0..|built|]) == 0;

  // second part is all zeros
  assert forall t :: |built| <= t < n ==> result[t] == 0;
  CountValZeros(result[|built|..n]);
  assert CountVal(0, result[|built|..n]) == n - |built|;

  // combine to conclude counts match
  assert CountVal(0, result[0..n]) == n - |built|;
  assert n - |built| == CountVal(0, xs[0..n]);
  assert CountVal(0, result[0..n]) == CountVal(0, xs[0..n]);

  // length preserved by construction
  assert xs.Length == result.Length;
}

// </vc-code>
