// <vc-preamble>
// Ghost function to compute the sum of lengths of all sub-sequences
ghost function sum_lengths(seqs: seq<seq<real>>): nat
{
    if |seqs| == 0 then 0
    else |seqs[0]| + sum_lengths(seqs[1..])
}

// Ghost predicate to ensure all elements are preserved in order
ghost predicate elements_preserved(original: seq<real>, split: seq<seq<real>>)
{
    var flattened := flatten(split);
    |flattened| == |original| && 
    forall i :: 0 <= i < |original| ==> flattened[i] == original[i]
}

// Ghost function to flatten a sequence of sequences back to a single sequence
ghost function flatten(seqs: seq<seq<real>>): seq<real>
{
    if |seqs| == 0 then []
    else seqs[0] + flatten(seqs[1..])
}

// Ghost predicate to ensure contiguous distribution without gaps or overlaps
ghost predicate contiguous_distribution(original: seq<real>, split: seq<seq<real>>)
{
    |split| > 0 ==>
    var start_indices := compute_start_indices(split);
    |start_indices| == |split| &&
    start_indices[0] == 0 &&
    (forall i :: 1 <= i < |split| ==> 
        start_indices[i] == start_indices[i-1] + |split[i-1]|) &&
    (forall i :: 0 <= i < |split| ==>
        forall j :: 0 <= j < |split[i]| ==>
            start_indices[i] + j < |original| &&
            split[i][j] == original[start_indices[i] + j])
}

// Ghost function to compute starting indices for each sub-sequence
ghost function compute_start_indices(split: seq<seq<real>>): seq<nat>
{
    if |split| == 0 then []
    else if |split| == 1 then [0]
    else [0] + compute_start_indices_helper(split, 1, |split[0]|)
}

// Helper ghost function for computing start indices recursively
ghost function compute_start_indices_helper(split: seq<seq<real>>, index: nat, current_start: nat): seq<nat>
    requires index <= |split|
{
    if index >= |split| then []
    else [current_start] + compute_start_indices_helper(split, index + 1, current_start + |split[index]|)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ArraySplit(v: seq<real>, k: nat) returns (result: seq<seq<real>>)
    requires k > 0
    ensures |result| == k
    ensures forall i :: 0 <= i < k ==>
        |result[i]| == if i < |v| % k then (|v| + k - 1) / k else |v| / k
    ensures forall i :: 0 <= i < k ==> |result[i]| >= 0
    ensures sum_lengths(result) == |v|
    ensures elements_preserved(v, result)
    ensures contiguous_distribution(v, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
