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
lemma CountLeafChildrenBounds(node: int, parents: seq<int>, n: int)
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
    ensures countLeafChildren(node, parents, n) >= 0
    ensures countLeafChildren(node, parents, n) <= n - 1
{
    var leafChildren := set i | 0 <= i < n - 1 && parents[i] - 1 == node && !hasChildren(i + 1, parents, n);
    var allIndices := set i {:trigger i in allIndices} | 0 <= i < n - 1;
    
    // Prove that |allIndices| == n - 1 by showing it's the set {0, 1, ..., n-2}
    assert forall i :: 0 <= i < n - 1 ==> i in allIndices;
    assert forall i :: i in allIndices ==> 0 <= i < n - 1;
    
    // The cardinality of {0, 1, ..., n-2} is n - 1
    assert allIndices == set i | 0 <= i < n - 1;
    assert |allIndices| == n - 1;
    
    // leafChildren is a subset of allIndices
    assert forall i :: i in leafChildren ==> i in allIndices;
    assert leafChildren <= allIndices;
    
    // Therefore |leafChildren| <= n - 1
    assert |leafChildren| <= |allIndices|;
    assert |leafChildren| <= n - 1;
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
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall node :: 0 <= node < i && hasChildren(node, parents, n) ==> 
            countLeafChildren(node, parents, n) >= 3
    {
        if hasChildren(i, parents, n) {
            var leafCount := 0;
            var j := 0;
            
            while j < n - 1
                invariant 0 <= j <= n - 1
                invariant leafCount == |set k | 0 <= k < j && parents[k] - 1 == i && !hasChildren(k + 1, parents, n)|
            {
                if parents[j] - 1 == i {
                    // Check if j+1 is a leaf (has no children)
                    var isLeaf := true;
                    var k := 0;
                    while k < n - 1
                        invariant 0 <= k <= n - 1
                        invariant isLeaf <==> (forall m :: 0 <= m < k ==> parents[m] - 1 != j + 1)
                    {
                        if parents[k] - 1 == j + 1 {
                            isLeaf := false;
                        }
                        k := k + 1;
                    }
                    
                    assert isLeaf == !hasChildren(j + 1, parents, n);
                    
                    if isLeaf {
                        leafCount := leafCount + 1;
                    }
                }
                j := j + 1;
            }
            
            assert leafCount == countLeafChildren(i, parents, n);
            
            if leafCount < 3 {
                result := "No";
                return;
            }
        }
        i := i + 1;
    }
    
    result := "Yes";
}
// </vc-code>

