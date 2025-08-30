//IMPL 
method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    ensures max >= 1
    ensures max <= nums.Length
    ensures exists seq :: is_increasing_subsequence(nums, seq) && |seq| == max
    ensures forall seq :: is_increasing_subsequence(nums, seq) ==> |seq| <= max
{
    var dp := new int[nums.Length];
    dp[0] := 1;
    max := 1;
    
    var i := 1;
    while i < nums.Length
        invariant 1 <= i <= nums.Length
        invariant max >= 1
        invariant forall k :: 0 <= k < i ==> dp[k] >= 1
        invariant forall k :: 0 <= k < i ==> dp[k] <= k + 1
        invariant max == max_in_range(dp, 0, i)
        invariant max <= i
        invariant exists k :: 0 <= k < i && dp[k] == max
        /* code modified by LLM (iteration 4): added invariant for dp correctness */
        invariant forall k :: 0 <= k < i ==> dp_represents_lis_length(nums, dp, k)
    {
        dp[i] := 1;
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant dp[i] >= 1
            invariant dp[i] <= i + 1
            /* code modified by LLM (iteration 4): strengthened inner loop invariant */
            invariant forall k :: 0 <= k < j ==> (nums[k] < nums[i] ==> dp[i] >= dp[k] + 1)
        {
            if nums[j] < nums[i] {
                dp[i] := find_max(dp[i], dp[j] + 1);
            }
            j := j + 1;
        }
        
        /* code modified by LLM (iteration 4): prove dp[i] correctness after inner loop */
        prove_dp_correctness(nums, dp, i);
        
        max := find_max(max, dp[i]);
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): call helper lemma to establish postconditions */
    establish_postconditions(nums, dp, max);
}

predicate is_increasing_subsequence(nums: array<int>, seq: seq<int>)
    reads nums
{
    |seq| >= 1 &&
    forall i :: 0 <= i < |seq| - 1 ==> seq[i] < seq[i + 1] &&
    exists indices :: |indices| == |seq| && 
        (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < nums.Length) &&
        (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i + 1]) &&
        (forall i :: 0 <= i < |seq| ==> seq[i] == nums[indices[i]])
}

function max_in_range(dp: array<int>, start: int, end: int): int
    reads dp
    requires 0 <= start < end <= dp.Length
    decreases end - start
{
    if start + 1 == end then dp[start]
    else find_max(dp[start], max_in_range(dp, start + 1, end))
}

/* code modified by LLM (iteration 4): added predicate to define dp correctness */
predicate dp_represents_lis_length(nums: array<int>, dp: array<int>, pos: int)
    reads nums, dp
    requires 0 <= pos < nums.Length
    requires dp.Length == nums.Length
{
    dp[pos] >= 1 &&
    exists seq :: is_increasing_subsequence_ending_at(nums, seq, pos) && |seq| == dp[pos] &&
    forall seq :: is_increasing_subsequence_ending_at(nums, seq, pos) ==> |seq| <= dp[pos]
}

/* code modified by LLM (iteration 4): added predicate for subsequences ending at specific position */
predicate is_increasing_subsequence_ending_at(nums: array<int>, seq: seq<int>, end_pos: int)
    reads nums
    requires 0 <= end_pos < nums.Length
{
    |seq| >= 1 &&
    forall i :: 0 <= i < |seq| - 1 ==> seq[i] < seq[i + 1] &&
    exists indices :: |indices| == |seq| && 
        (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < nums.Length) &&
        (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i + 1]) &&
        (forall i :: 0 <= i < |seq| ==> seq[i] == nums[indices[i]]) &&
        indices[|indices| - 1] == end_pos
}

/* code modified by LLM (iteration 4): added lemma to prove dp correctness */
lemma prove_dp_correctness(nums: array<int>, dp: array<int>, pos: int)
    requires 0 < pos < nums.Length
    requires dp.Length == nums.Length
    requires dp[pos] >= 1
    requires forall k :: 0 <= k < pos ==> dp_represents_lis_length(nums, dp, k)
    requires forall k :: 0 <= k < pos ==> (nums[k] < nums[pos] ==> dp[pos] >= dp[k] + 1)
    ensures dp_represents_lis_length(nums, dp, pos)
{
    /* code modified by LLM (iteration 4): construct witness sequence */
    var base_seq := [nums[pos]];
    var base_indices := [pos];
    assert is_increasing_subsequence_ending_at(nums, base_seq, pos);
    
    /* code modified by LLM (iteration 4): find optimal previous position */
    var best_length := 1;
    var k := 0;
    while k < pos
        invariant 0 <= k <= pos
        invariant best_length >= 1
        invariant exists seq :: is_increasing_subsequence_ending_at(nums, seq, pos) && |seq| == best_length
        invariant forall j :: 0 <= j < k ==> (nums[j] < nums[pos] ==> best_length >= dp[j] + 1)
    {
        if nums[k] < nums[pos] {
            assert dp_represents_lis_length(nums, dp, k);
            var prev_seq :| is_increasing_subsequence_ending_at(nums, prev_seq, k) && |prev_seq| == dp[k];
            var extended_seq := prev_seq + [nums[pos]];
            
            /* code modified by LLM (iteration 4): verify extended sequence is valid */
            var prev_indices :| |prev_indices| == |prev_seq| && 
                (forall i :: 0 <= i < |prev_indices| ==> 0 <= prev_indices[i] < nums.Length) &&
                (forall i :: 0 <= i < |prev_indices| - 1 ==> prev_indices[i] < prev_indices[i + 1]) &&
                (forall i :: 0 <= i < |prev_seq| ==> prev_seq[i] == nums[prev_indices[i]]) &&
                prev_indices[|prev_indices| - 1] == k;
            
            var new_indices := prev_indices + [pos];
            assert is_increasing_subsequence_ending_at(nums, extended_seq, pos);
            assert |extended_seq| == dp[k] + 1;
            
            if dp[k] + 1 > best_length {
                best_length := dp[k] + 1;
            }
        }
        k := k + 1;
    }
    
    assert dp[pos] >= best_length;
    
    /* code modified by LLM (iteration 4): prove optimality */
    forall seq | is_increasing_subsequence_ending_at(nums, seq, pos)
        ensures |seq| <= dp[pos]
    {
        if |seq| == 1 {
            assert |seq| <= dp[pos];
        } else {
            var indices :| |indices| == |seq| && 
                (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < nums.Length) &&
                (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i + 1]) &&
                (forall i :: 0 <= i < |seq| ==> seq[i] == nums[indices[i]]) &&
                indices[|indices| - 1] == pos;
            
            var second_last := indices[|indices| - 2];
            var prefix_seq := seq[..|seq|-1];
            assert is_increasing_subsequence_ending_at(nums, prefix_seq, second_last);
            assert dp_represents_lis_length(nums, dp, second_last);
            assert |prefix_seq| <= dp[second_last];
            assert nums[second_last] < nums[pos];
            assert dp[pos] >= dp[second_last] + 1;
            assert |seq| == |prefix_seq| + 1 <= dp[second_last] + 1 <= dp[pos];
        }
    }
}

/* code modified by LLM (iteration 4): simplified lemma to establish postconditions */
lemma establish_postconditions(nums: array<int>, dp: array<int>, max: int)
    requires nums.Length >= 1
    requires dp.Length == nums.Length
    requires forall k :: 0 <= k < nums.Length ==> dp[k] >= 1
    requires exists k :: 0 <= k < nums.Length && dp[k] == max
    requires forall k :: 0 <= k < nums.Length ==> dp_represents_lis_length(nums, dp, k)
    ensures exists seq :: is_increasing_subsequence(nums, seq) && |seq| == max
    ensures forall seq :: is_increasing_subsequence(nums, seq) ==> |seq| <= max
{
    var k :| 0 <= k < nums.Length && dp[k] == max;
    
    /* code modified by LLM (iteration 4): use dp correctness to get existence */
    assert dp_represents_lis_length(nums, dp, k);
    var witness_seq :| is_increasing_subsequence_ending_at(nums, witness_seq, k) && |witness_seq| == dp[k];
    
    /* code modified by LLM (iteration 4): show witness satisfies general predicate */
    assert is_increasing_subsequence(nums, witness_seq);
    assert |witness_seq| == max;
    
    /* code modified by LLM (iteration 4): prove maximality */
    forall seq | is_increasing_subsequence(nums, seq)
        ensures |seq| <= max
    {
        if |seq| > 0 {
            var indices :| |indices| == |seq| && 
                (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < nums.Length) &&
                (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i + 1]) &&
                (forall i :: 0 <= i < |seq| ==> seq[i] == nums[indices[i]]);
            
            var last_pos := indices[|indices| - 1];
            assert is_increasing_subsequence_ending_at(nums, seq, last_pos);
            assert dp_represents_lis_length(nums, dp, last_pos);
            assert |seq| <= dp[last_pos];
            assert dp[last_pos] <= max;
        }
    }
}

//ATOM 
function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}