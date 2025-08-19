predicate correct_pair(pair: (int, int), nums: seq<int>, target: int)
{
    var (i, j) := pair;
    0 <= i < |nums| && 0 <= j < |nums| && i != j && nums[i] + nums[j] == target
}

// We actually make a weaker pre-condition: there exists at least one solution.
// For verification simplicity, we pretend as if:
// - `seq` were Python list
// - `map` were Python dict
method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
 requires exists i, j :: correct_pair((i, j), nums, target)
 ensures correct_pair(pair, nums, target)
{
    var e_to_i: map<int, int> := map[];
    var i := 0;
    
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant forall k :: k in e_to_i ==> exists i' :: 0 <= i' < i && nums[i'] == k && e_to_i[k] == i'
        invariant forall i' :: 0 <= i' < i ==> nums[i'] in e_to_i
        /* code modified by LLM (iteration 1): Fixed indentation and added parentheses to exists expression */
        invariant (exists a, b :: correct_pair((a, b), nums, target) && 
                   (a < i ==> nums[a] in e_to_i) && 
                   (b < i ==> nums[b] in e_to_i) &&
                   (a < i && b < i ==> false))
    {
        var complement := target - nums[i];
        
        if complement in e_to_i {
            var j := e_to_i[complement];
            /* code modified by LLM (iteration 1): Added assertions to prove the found pair is correct */
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
    
    /* code modified by LLM (iteration 1): Handle the unreachable case with a proof by contradiction */
    // This point should be unreachable due to the precondition
    assert i == |nums|;
    assert exists a, b :: correct_pair((a, b), nums, target);
    // By the loop invariant, if a solution exists and we've processed all elements,
    // we should have found it in the loop
    assert false;
    pair := (0, 0); // unreachable, but needed for compilation
}

/* Discussions
 but this is wrong, because `nums` may contain redundant elements.
 Redundant elements will share the same key in `e_to_i`, the newer overwriting the older.
 
 To specify a set/map, we often need "back and forth" assertions, namely:
 (a) What elements are in the map/set (like in formula A)
 (b) What do elements in the set/map satisfy (like in formula B)
*/