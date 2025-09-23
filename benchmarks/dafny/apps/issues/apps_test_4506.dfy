// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>, b: seq<int>) {
    n >= 1 && |a| == n && |b| == n &&
    (forall i :: 0 <= i < n ==> 1 <= a[i] <= 1000000) &&
    (forall i :: 0 <= i < n ==> 1 <= b[i] <= 1000000)
}

predicate IsPermutation(perm: seq<int>, original: seq<int>) {
    |perm| == |original| && multiset(perm) == multiset(original)
}

predicate ValidOutput(result: int) {
    0 <= result < 998244353
}
// </vc-preamble>

// <vc-helpers>
method SortIndicesByWeights(indices: seq<int>, weights: seq<int>) returns (sorted: seq<int>)
    requires |indices| == |weights|
    requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |weights|
    requires forall i, j :: 0 <= i < j < |indices| ==> indices[i] != indices[j]
    ensures |sorted| == |indices|
    ensures multiset(sorted) == multiset(indices)
    ensures forall i :: 0 <= i < |sorted| ==> 0 <= sorted[i] < |weights|
    ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] != sorted[j]
    ensures forall i, j :: 0 <= i < j < |sorted| ==> weights[sorted[i]] <= weights[sorted[j]]
{
    sorted := indices;
    for i := 0 to |sorted| 
        invariant 0 <= i <= |sorted|
        invariant |sorted| == |indices|
        invariant multiset(sorted) == multiset(indices)
        invariant forall k :: 0 <= k < |sorted| ==> 0 <= sorted[k] < |weights|
        invariant forall p, q :: 0 <= p < q < |sorted| ==> sorted[p] != sorted[q]
        invariant forall j, k :: 0 <= j < k < i ==> weights[sorted[j]] <= weights[sorted[k]]
        invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> weights[sorted[j]] <= weights[sorted[k]]
    {
        var minIdx := i;
        for j := i + 1 to |sorted| 
            invariant i + 1 <= j <= |sorted|
            invariant |sorted| == |indices|
            invariant multiset(sorted) == multiset(indices)
            invariant forall k :: 0 <= k < |sorted| ==> 0 <= sorted[k] < |weights|
            invariant forall p, q :: 0 <= p < q < |sorted| ==> sorted[p] != sorted[q]
            invariant forall p, q :: 0 <= p < q < i ==> weights[sorted[p]] <= weights[sorted[q]]
            invariant forall p :: 0 <= p < i ==> forall k :: i <= k < |sorted| ==> weights[sorted[p]] <= weights[sorted[k]]
            invariant i <= minIdx < |sorted|
            invariant forall k :: i <= k < j ==> weights[sorted[minIdx]] <= weights[sorted[k]]
        {
            if weights[sorted[j]] < weights[sorted[minIdx]] {
                minIdx := j;
            }
        }
        if minIdx != i {
            var temp := sorted[i];
            sorted := sorted[i := sorted[minIdx]][minIdx := temp];
        }
    }
}

method SortDescending(arr: seq<int>) returns (sorted: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> 1 <= arr[i] <= 1000000
    ensures |sorted| == |arr|
    ensures multiset(sorted) == multiset(arr)
    ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
    ensures forall i :: 0 <= i < |sorted| ==> 1 <= sorted[i] <= 1000000
{
    sorted := arr;
    for i := 0 to |sorted| 
        invariant 0 <= i <= |sorted|
        invariant |sorted| == |arr|
        invariant multiset(sorted) == multiset(arr)
        invariant forall j, k :: 0 <= j < k < i ==> sorted[j] >= sorted[k]
        invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> sorted[j] >= sorted[k]
        invariant forall j :: 0 <= j < |sorted| ==> 1 <= sorted[j] <= 1000000
    {
        var maxIdx := i;
        for j := i + 1 to |sorted| 
            invariant i + 1 <= j <= |sorted|
            invariant |sorted| == |arr|
            invariant multiset(sorted) == multiset(arr)
            invariant forall p, q :: 0 <= p < q < i ==> sorted[p] >= sorted[q]
            invariant forall p :: 0 <= p < i ==> forall k :: i <= k < |sorted| ==> sorted[p] >= sorted[k]
            invariant i <= maxIdx < |sorted|
            invariant forall k :: i <= k < j ==> sorted[maxIdx] >= sorted[k]
            invariant forall k :: 0 <= k < |sorted| ==> 1 <= sorted[k] <= 1000000
        {
            if sorted[j] > sorted[maxIdx] {
                maxIdx := j;
            }
        }
        if maxIdx != i {
            var temp := sorted[i];
            sorted := sorted[i := sorted[maxIdx]][maxIdx := temp];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, b: seq<int>) returns (result: int)
    requires ValidInput(n, a, b)
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    var m := 998244353;

    // Create array of (weight, index) pairs where weight = a[i] * (n - i) * (i + 1)
    var weights := seq(n, i requires 0 <= i < n => a[i] * (n - i) * (i + 1));
    var indices := seq(n, i => i);

    // Sort indices by weights (ascending)
    var aord := SortIndicesByWeights(indices, weights);

    // Sort b in descending order
    var sorted_b := SortDescending(b);

    // Create new_b by pairing smallest weights with largest b values
    var new_b := seq(n, i => 0);
    for i := 0 to n 
        invariant 0 <= i <= n
        invariant |new_b| == n
        invariant forall j :: 0 <= j < n ==> 0 <= new_b[j] <= 1000000
        invariant forall j :: 0 <= j < i ==> 0 <= aord[j] < n
        invariant forall j, k :: 0 <= j < k < i ==> aord[j] != aord[k]
        invariant forall j :: 0 <= j < i ==> new_b[aord[j]] == sorted_b[j]
    {
        new_b := new_b[aord[i] := sorted_b[i]];
    }

    // Compute final answer
    result := 0;
    for i := 0 to n 
        invariant 0 <= i <= n
        invariant 0 <= result < m
    {
        var term1 := (a[i] % m * new_b[i] % m) % m;
        var term2 := (term1 * (n - i) % m) % m;
        var contribution := (term2 * (i + 1) % m) % m;
        result := (result + contribution) % m;
    }
}
// </vc-code>
