function hasChildren(node: int, parents: seq<int>, n: int): bool
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
{
    exists i :: 0 <= i < n - 1 && parents[i] - 1 == node
}

function countLeafChildren(node: int, parents: seq<int>, n: int): int
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
{
    |set i | 0 <= i < n - 1 && parents[i] - 1 == node && !hasChildren(i + 1, parents, n)|
}

predicate ValidInput(n: int, parents: seq<int>)
{
    n >= 3 && |parents| == n - 1 && 
    (forall i :: 0 <= i < n - 1 ==> 1 <= parents[i] <= i + 1)
}

predicate IsSpruce(n: int, parents: seq<int>)
    requires ValidInput(n, parents)
{
    forall node :: 0 <= node < n && hasChildren(node, parents, n) ==> 
        countLeafChildren(node, parents, n) >= 3
}

// <vc-helpers>
lemma LeafChildrenCountCorrect(node: int, parents: seq<int>, n: int, count: int)
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
    requires count == |set i | 0 <= i < n - 1 && parents[i] - 1 == node && !hasChildren(i + 1, parents, n)|
    ensures count == countLeafChildren(node, parents, n)
{
}

lemma HasChildrenEquivalence(node: int, parents: seq<int>, n: int, found: bool)
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
    requires found == (exists i :: 0 <= i < n - 1 && parents[i] - 1 == node)
    ensures found == hasChildren(node, parents, n)
{
}

lemma LeafChildCountInvariantHelper(node: int, parents: seq<int>, n: int, j: int, leafChildCount: int)
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
    requires 0 <= j <= n - 1
    requires leafChildCount == |set k | 0 <= k < j && parents[k] - 1 == node && !hasChildren(k + 1, parents, n)|
    ensures leafChildCount <= j
{
}

lemma LeafChildCountIncrement(node: int, parents: seq<int>, n: int, j: int, leafChildCount: int)
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
    requires 0 <= j < n - 1
    requires leafChildCount == |set k | 0 <= k < j && parents[k] - 1 == node && !hasChildren(k + 1, parents, n)|
    requires parents[j] - 1 == node
    requires !hasChildren(j + 1, parents, n)
    ensures leafChildCount + 1 == |set k | 0 <= k < j + 1 && parents[k] - 1 == node && !hasChildren(k + 1, parents, n)|
{
    var oldSet := set k | 0 <= k < j && parents[k] - 1 == node && !hasChildren(k + 1, parents, n);
    var newSet := set k | 0 <= k < j + 1 && parents[k] - 1 == node && !hasChildren(k + 1, parents, n);
    assert newSet == oldSet + {j};
    assert j !in oldSet;
}

lemma LeafChildCountNoIncrement(node: int, parents: seq<int>, n: int, j: int, leafChildCount: int)
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
    requires 0 <= j < n - 1
    requires leafChildCount == |set k | 0 <= k < j && parents[k] - 1 == node && !hasChildren(k + 1, parents, n)|
    requires !(parents[j] - 1 == node && !hasChildren(j + 1, parents, n))
    ensures leafChildCount == |set k | 0 <= k < j + 1 && parents[k] - 1 == node && !hasChildren(k + 1, parents, n)|
{
    var oldSet := set k | 0 <= k < j && parents[k] - 1 == node && !hasChildren(k + 1, parents, n);
    var newSet := set k | 0 <= k < j + 1 && parents[k] - 1 == node && !hasChildren(k + 1, parents, n);
    assert newSet == oldSet;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, parents: seq<int>) returns (result: string)
    requires ValidInput(n, parents)
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> IsSpruce(n, parents)
// </vc-spec>
// <vc-code>
{
    var allNodesAreSpruce := true;
    var node := 0;
    
    while node < n && allNodesAreSpruce
        invariant 0 <= node <= n
        invariant allNodesAreSpruce ==> (forall k :: 0 <= k < node && hasChildren(k, parents, n) ==> countLeafChildren(k, parents, n) >= 3)
        invariant !allNodesAreSpruce ==> !IsSpruce(n, parents)
    {
        var nodeHasChildren := false;
        var i := 0;
        
        while i < n - 1
            invariant 0 <= i <= n - 1
            invariant nodeHasChildren == (exists j :: 0 <= j < i && parents[j] - 1 == node)
        {
            if parents[i] - 1 == node {
                nodeHasChildren := true;
            }
            i := i + 1;
        }
        
        HasChildrenEquivalence(node, parents, n, nodeHasChildren);
        
        if nodeHasChildren {
            var leafChildCount := 0;
            var j := 0;
            
            while j < n - 1
                invariant 0 <= j <= n - 1
                invariant leafChildCount == |set k | 0 <= k < j && parents[k] - 1 == node && !hasChildren(k + 1, parents, n)|
                invariant leafChildCount <= j
            {
                var currentElementInSet := parents[j] - 1 == node && !hasChildren(j + 1, parents, n);
                
                if parents[j] - 1 == node {
                    var childHasChildren := false;
                    var k := 0;
                    
                    while k < n - 1
                        invariant 0 <= k <= n - 1
                        invariant childHasChildren == (exists m :: 0 <= m < k && parents[m] - 1 == j + 1)
                    {
                        if parents[k] - 1 == j + 1 {
                            childHasChildren := true;
                        }
                        k := k + 1;
                    }
                    
                    HasChildrenEquivalence(j + 1, parents, n, childHasChildren);
                    
                    if !childHasChildren {
                        LeafChildCountIncrement(node, parents, n, j, leafChildCount);
                        leafChildCount := leafChildCount + 1;
                    } else {
                        LeafChildCountNoIncrement(node, parents, n, j, leafChildCount);
                    }
                } else {
                    assert !currentElementInSet;
                    LeafChildCountNoIncrement(node, parents, n, j, leafChildCount);
                }
                
                assert leafChildCount == |set k | 0 <= k < j + 1 && parents[k] - 1 == node && !hasChildren(k + 1, parents, n)|;
                j := j + 1;
            }
            
            LeafChildrenCountCorrect(node, parents, n, leafChildCount);
            
            if leafChildCount < 3 {
                allNodesAreSpruce := false;
            }
        }
        
        node := node + 1;
    }
    
    if allNodesAreSpruce {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

