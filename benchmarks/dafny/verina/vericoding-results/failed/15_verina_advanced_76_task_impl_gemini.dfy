// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [fixed syntax error in lemma precondition] */
lemma MaintainTopKInvariant(counts: map<int, nat>, picked: set<int>, remaining: set<int>, max_elem: int)
    requires forall c | c in remaining + picked :: c in counts
    requires picked # remaining
    requires forall p in picked, r in remaining :: counts[r] <= counts[p]
    requires max_elem in remaining
    requires forall r in remaining :: counts[r] <= counts[max_elem]
    ensures forall p in picked + {max_elem}, r in remaining - {max_elem} :: counts[r] <= counts[p]
{}

function CountFrequencies(s: seq<int>): map<int, nat>
    decreases |s|
{
    if |s| == 0 then map[]
    else
        var counts_rest := CountFrequencies(s[1..]);
        var head := s[0];
        if head in counts_rest 
        then counts_rest[head := counts_rest[head] + 1]
        else counts_rest[head := 1]
}

lemma CountFrequenciesKeysLemma(s: seq<int>)
    ensures CountFrequencies(s).Keys == (set x | x in s)
    decreases |s|
{
    if |s| > 0 {
        CountFrequenciesKeysLemma(s[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method TopKFrequent(nums: array<int>, k: nat) returns (result: array<int>)
    requires k <= |set i | 0 <= i < nums.Length :: nums[i]|
    ensures result.Length == k
    ensures forall x :: x in result[..] ==> x in nums[..]
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [no functional change; error was in helper] */
    var counts := CountFrequencies(nums[..]);
    CountFrequenciesKeysLemma(nums[..]);
    
    var remaining_candidates := counts.Keys;
    result := new int[k];
    ghost var picked_elements: set<int> := {};
    
    for i := 0..k
        invariant 0 <= i <= k
        invariant result.Length == k
        invariant |picked_elements| == i
        invariant picked_elements <= counts.Keys
        invariant remaining_candidates == counts.Keys - picked_elements
        invariant forall p, r :: p in picked_elements && r in remaining_candidates ==> counts[r] <= counts[p]
        invariant forall j :: 0 <= j < i ==> result[j] in picked_elements
        invariant |{result[j] | 0 <= j < i}| == i
    {
        // this requires remaining_candidates to be non-empty, which is true because i < k and k <= |counts.Keys|
        var max_elem :| max_elem in remaining_candidates && 
                       forall r :: r in remaining_candidates ==> counts[r] <= counts[max_elem];

        MaintainTopKInvariant(counts, picked_elements, remaining_candidates, max_elem);

        result[i] := max_elem;
        
        picked_elements := picked_elements + {max_elem};
        remaining_candidates := remaining_candidates - {max_elem};
    }
}
// </vc-code>
