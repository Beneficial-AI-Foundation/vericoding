//IMPL twoSum

predicate correct_pair(pair: (int, int), nums: seq<int>, target: int)
{
    var (i, j) := pair;
    0 <= i < |nums| && 0 <= j < |nums| && i != j && nums[i] + nums[j] == target
}

method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
 requires exists i, j :: correct_pair((i, j), nums, target)
 ensures correct_pair(pair, nums, target)
{
    var e_to_i: map<int, int> := map[];
    var i := 0;
    
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant forall k :: k in e_to_i ==> exists idx :: 0 <= idx < i && nums[idx] == k
        invariant forall idx :: 0 <= idx < i ==> nums[idx] in e_to_i
        /* code modified by LLM (iteration 1): added invariant to establish map values correspond to correct indices */
        invariant forall k :: k in e_to_i ==> 0 <= e_to_i[k] < i && nums[e_to_i[k]] == k
        /* code modified by LLM (iteration 1): added invariant to ensure solution exists if not found yet */
        invariant exists ii, jj :: correct_pair((ii, jj), nums, target) && (jj >= i || ii >= i)
    {
        var complement := target - nums[i];
        
        if complement in e_to_i {
            var j := e_to_i[complement];
            /* code modified by LLM (iteration 1): added assertions to help Dafny verify the solution is correct */
            assert nums[j] == complement;
            assert nums[j] + nums[i] == target;
            assert 0 <= j < i < |nums|;
            assert j != i;
            pair := (j, i);
            return;
        }
        
        e_to_i := e_to_i[nums[i] := i];
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to prove this point is unreachable */
    assert false;
    pair := (0, 1);
}