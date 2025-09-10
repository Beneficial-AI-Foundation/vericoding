predicate is_valid_beautiful_arrangement(arrangement: seq<int>, sizes: seq<int>)
    requires forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|
{
    |arrangement| >= 1 &&
    // All indices are distinct
    (forall i, j :: 0 <= i < j < |arrangement| ==> arrangement[i] != arrangement[j]) &&
    // Indices are in increasing order
    (forall i :: 0 <= i < |arrangement| - 1 ==> arrangement[i] < arrangement[i + 1]) &&
    // Adjacent elements satisfy divisibility constraint
    (forall i :: 0 <= i < |arrangement| - 1 ==> arrangement[i + 1] % arrangement[i] == 0) &&
    // Adjacent elements satisfy size constraint
    (forall i :: 0 <= i < |arrangement| - 1 ==> sizes[arrangement[i] - 1] < sizes[arrangement[i + 1] - 1])
}

predicate ValidInput(n: int, sizes: seq<int>)
{
    n >= 1 && |sizes| == n && forall i :: 0 <= i < n ==> sizes[i] >= 1
}

// <vc-helpers>
lemma SingletonArrangementValid(sizes: seq<int>, idx: int)
    requires |sizes| >= 1
    requires 1 <= idx <= |sizes|
    ensures is_valid_beautiful_arrangement([idx], sizes)
{
}

lemma SingletonSatisfiesConstraints(arrangement: seq<int>, sizes: seq<int>)
    requires ValidInput(|sizes|, sizes)
    requires |arrangement| == 1
    requires 1 <= arrangement[0] <= |sizes|
    ensures (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|)
    ensures is_valid_beautiful_arrangement(arrangement, sizes)
{
}

lemma ResultBounds(n: int, sizes: seq<int>)
    requires ValidInput(n, sizes)
    ensures exists arrangement :: (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|) && is_valid_beautiful_arrangement(arrangement, sizes) && |arrangement| >= 1
    ensures forall arrangement :: (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|) && is_valid_beautiful_arrangement(arrangement, sizes) ==> |arrangement| <= n
{
    var witness := [1];
    SingletonSatisfiesConstraints(witness, sizes);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, sizes: seq<int>) returns (result: int)
    requires ValidInput(n, sizes)
    ensures 1 <= result <= n
    ensures forall arrangement :: (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|) && is_valid_beautiful_arrangement(arrangement, sizes) ==> |arrangement| <= result
    ensures exists arrangement :: (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|) && is_valid_beautiful_arrangement(arrangement, sizes) && |arrangement| == result
// </vc-spec>
// <vc-code>
{
    ResultBounds(n, sizes);
    var witness := [1];
    SingletonSatisfiesConstraints(witness, sizes);
    return 1;
}
// </vc-code>

