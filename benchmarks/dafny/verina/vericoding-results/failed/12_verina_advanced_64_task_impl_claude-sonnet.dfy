// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed FilterElementExists lemma to properly handle existence requirements */
function FilterNonTarget(lst: seq<nat>, target: nat): seq<nat>
{
    if |lst| == 0 then []
    else if lst[0] == target then FilterNonTarget(lst[1..], target)
    else [lst[0]] + FilterNonTarget(lst[1..], target)
}

lemma FilterPreservesOrder(lst: seq<nat>, target: nat)
    ensures forall i, j :: 0 <= i < j < |lst| && lst[i] != target && lst[j] != target ==>
        (exists k1, k2 :: 0 <= k1 < k2 < |FilterNonTarget(lst, target)| &&
         FilterNonTarget(lst, target)[k1] == lst[i] && FilterNonTarget(lst, target)[k2] == lst[j])
{
    if |lst| <= 1 {
        return;
    }
    
    var filtered := FilterNonTarget(lst, target);
    var tail_filtered := FilterNonTarget(lst[1..], target);
    
    FilterPreservesOrder(lst[1..], target);
    
    forall i, j | 0 <= i < j < |lst| && lst[i] != target && lst[j] != target
    ensures exists k1, k2 :: 0 <= k1 < k2 < |filtered| && filtered[k1] == lst[i] && filtered[k2] == lst[j]
    {
        if i == 0 {
            if lst[0] != target {
                assert filtered == [lst[0]] + tail_filtered;
                assert filtered[0] == lst[0] == lst[i];
                var j_in_tail := j - 1;
                assert 0 <= j_in_tail < |lst[1..]| && lst[1..][j_in_tail] == lst[j];
                assert lst[j] != target;
                
                FilterElementExists(lst[1..], target, lst[j]);
                
                var k2_tail :| 0 <= k2_tail < |tail_filtered| && tail_filtered[k2_tail] == lst[j];
                var k2 := k2_tail + 1;
                assert 1 <= k2 < |filtered| && filtered[k2] == lst[j];
                assert 0 < k2 && filtered[0] == lst[i] && filtered[k2] == lst[j];
            }
        } else {
            var i_in_tail := i - 1;
            var j_in_tail := j - 1;
            assert 0 <= i_in_tail < j_in_tail < |lst[1..]|;
            assert lst[1..][i_in_tail] == lst[i] && lst[1..][j_in_tail] == lst[j];
            assert lst[i] != target && lst[j] != target;
            var k1_tail, k2_tail :| 0 <= k1_tail < k2_tail < |tail_filtered| && tail_filtered[k1_tail] == lst[i] && tail_filtered[k2_tail] == lst[j];
            if lst[0] == target {
                assert filtered == tail_filtered;
                assert filtered[k1_tail] == lst[i] && filtered[k2_tail] == lst[j];
            } else {
                assert filtered == [lst[0]] + tail_filtered;
                var k1 := k1_tail + 1;
                var k2 := k2_tail + 1;
                assert 1 <= k1 < k2 < |filtered| && filtered[k1] == lst[i] && filtered[k2] == lst[j];
            }
        }
    }
}

lemma FilterElementExists(lst: seq<nat>, target: nat, elem: nat)
    requires elem != target
    requires exists i :: 0 <= i < |lst| && lst[i] == elem
    ensures exists k :: 0 <= k < |FilterNonTarget(lst, target)| && FilterNonTarget(lst, target)[k] == elem
{
    if |lst| == 0 {
        return;
    }
    
    var i_witness :| 0 <= i_witness < |lst| && lst[i_witness] == elem;
    var filtered := FilterNonTarget(lst, target);
    
    if lst[0] == target {
        if i_witness > 0 {
            assert lst[1..][i_witness - 1] == elem;
            FilterElementExists(lst[1..], target, elem);
        }
    } else {
        if i_witness == 0 {
            assert filtered[0] == elem;
        } else {
            assert lst[1..][i_witness - 1] == elem;
            FilterElementExists(lst[1..], target, elem);
            var k_tail :| 0 <= k_tail < |FilterNonTarget(lst[1..], target)| && FilterNonTarget(lst[1..], target)[k_tail] == elem;
            var k := k_tail + 1;
            assert filtered[k] == elem;
        }
    }
}

lemma FilterNoTarget(lst: seq<nat>, target: nat)
    ensures forall i :: 0 <= i < |FilterNonTarget(lst, target)| ==> FilterNonTarget(lst, target)[i] != target
{
    if |lst| == 0 {
        return;
    }
    FilterNoTarget(lst[1..], target);
    
    var filtered := FilterNonTarget(lst, target);
    if lst[0] == target {
        assert filtered == FilterNonTarget(lst[1..], target);
    } else {
        assert filtered == [lst[0]] + FilterNonTarget(lst[1..], target);
        assert filtered[0] == lst[0] != target;
    }
}

lemma FilterFromOriginal(lst: seq<nat>, target: nat)
    ensures forall i :: 0 <= i < |FilterNonTarget(lst, target)| ==>
        exists j :: 0 <= j < |lst| && lst[j] == FilterNonTarget(lst, target)[i] && lst[j] != target
{
    if |lst| == 0 {
        return;
    }
    FilterFromOriginal(lst[1..], target);
    
    var filtered := FilterNonTarget(lst, target);
    if lst[0] == target {
        assert filtered == FilterNonTarget(lst[1..], target);
        forall i | 0 <= i < |filtered|
        ensures exists j :: 0 <= j < |lst| && lst[j] == filtered[i] && lst[j] != target
        {
            var j_tail :| 0 <= j_tail < |lst[1..]| && lst[1..][j_tail] == filtered[i] && lst[1..][j_tail] != target;
            var j := j_tail + 1;
            assert 0 <= j < |lst| && lst[j] == filtered[i] && lst[j] != target;
        }
    } else {
        assert filtered == [lst[0]] + FilterNonTarget(lst[1..], target);
        assert filtered[0] == lst[0];
        forall i | 0 <= i < |filtered|
        ensures exists j :: 0 <= j < |lst| && lst[j] == filtered[i] && lst[j] != target
        {
            if i == 0 {
                assert lst[0] == filtered[i] && lst[0] != target;
            } else {
                var tail_idx := i - 1;
                assert 0 <= tail_idx < |FilterNonTarget(lst[1..], target)|;
                var j_tail :| 0 <= j_tail < |lst[1..]| && lst[1..][j_tail] == filtered[i] && lst[1..][j_tail] != target;
                var j := j_tail + 1;
                assert 0 <= j < |lst| && lst[j] == filtered[i] && lst[j] != target;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method RemoveElement(lst: seq<nat>, target: nat) returns (result: seq<nat>)
    ensures
        forall i :: 0 <= i < |result| ==> result[i] != target
    ensures
        forall i :: 0 <= i < |result| ==> 
            exists j :: 0 <= j < |lst| && lst[j] == result[i] && lst[j] != target
    ensures
        forall i, j :: 0 <= i < j < |lst| && lst[i] != target && lst[j] != target ==> 
            (exists k1, k2 :: 0 <= k1 < k2 < |result| && 
            result[k1] == lst[i] && result[k2] == lst[j])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): same method body with proper helper lemma calls */
{
    result := FilterNonTarget(lst, target);
    FilterNoTarget(lst, target);
    FilterFromOriginal(lst, target);
    FilterPreservesOrder(lst, target);
}
// </vc-code>
