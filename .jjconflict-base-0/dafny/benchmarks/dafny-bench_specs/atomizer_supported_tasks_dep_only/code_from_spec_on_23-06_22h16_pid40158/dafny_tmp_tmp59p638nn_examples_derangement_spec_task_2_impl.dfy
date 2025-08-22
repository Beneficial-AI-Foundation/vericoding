//ATOM derangement
predicate derangement(s: seq<nat>)
{
    forall i :: 0 <= i < |s| ==> s[i] != i
}

//ATOM permutation
predicate permutation(s: seq<nat>)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> 0 <= s[i] < |s|) &&
    (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
}

//ATOM multisetRange
function multisetRange(n: nat): multiset<nat>
{
    if n == 0 then multiset{} else multisetRange(n-1) + multiset{n-1}
}

//ATOM distinct
predicate distinct(s: seq<nat>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

//ATOM test
method test()
{
    // Empty test method
}

//IMPL unknown_522
method unknown_522(links: seq<nat>)
    requires |links| > 0
    requires permutation(links)
    requires derangement(links)
    requires distinct(links)
{
    var qAct: nat := links[0];
    var i : nat := 0;
    ghost var oldIndex := 0;
    /* code modified by LLM (iteration 1): Simplify ghost variables - remove complex indices tracking */
    ghost var visited: multiset<nat> := multiset{};

    while qAct != 0
        /* code modified by LLM (iteration 1): Ensure qAct is valid index */
        invariant 0 <= qAct < |links|
        invariant i >= 0
        /* code modified by LLM (iteration 1): Track visited elements within bounds */
        invariant visited <= multisetRange(|links|)
        invariant |visited| == i
        /* code modified by LLM (iteration 1): Ensure qAct not in visited (prevents infinite loops) */
        invariant qAct !in visited
        /* code modified by LLM (iteration 1): Since qAct != 0 and not visited, i < |links| - 1 */
        invariant i < |links| - 1
        /* code modified by LLM (iteration 1): Use remaining unvisited elements for termination */
        decreases |links| - i - 1
    {
        /* code modified by LLM (iteration 1): Store current qAct before updating */
        ghost var currentqAct := qAct;
        oldIndex := qAct;
        /* code modified by LLM (iteration 1): Add current qAct to visited set */
        visited := visited + multiset{qAct};
        /* code modified by LLM (iteration 1): Get next element - qAct is valid by invariant */
        qAct := links[qAct];
        i := i + 1;
        
        /* code modified by LLM (iteration 1): Assert qAct is valid after update */
        assert 0 <= qAct < |links| by {
            assert permutation(links);
            assert 0 <= oldIndex < |links|;
            assert 0 <= links[oldIndex] < |links|;
        }
    }
}