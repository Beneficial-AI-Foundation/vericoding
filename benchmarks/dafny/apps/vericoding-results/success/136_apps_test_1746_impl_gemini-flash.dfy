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
lemma lemma_HasChildrenEquivalence(node: int, parents: seq<int>, n: int)
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
    ensures hasChildren(node, parents, n) <==> (exists i :: 0 <= i < n - 1 && parents[i] - 1 == node)
{}

lemma lemma_CountLeafChildrenEquivalence(node: int, parents: seq<int>, n: int)
    requires 0 <= node < n
    requires n >= 3
    requires |parents| == n - 1
    ensures countLeafChildren(node, parents, n) == |set i | 0 <= i < n - 1 && parents[i] - 1 == node && !hasChildren(i + 1, parents, n)|
{}

lemma lemma_IsSpruceDefinition(n: int, parents: seq<int>)
    requires ValidInput(n, parents)
    ensures IsSpruce(n, parents) <==> (forall node :: 0 <= node < n && hasChildren(node, parents, n) ==> countLeafChildren(node, parents, n) >= 3)
{}
// </vc-helpers>

// <vc-spec>
method solve(n: int, parents: seq<int>) returns (result: string)
    requires ValidInput(n, parents)
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> IsSpruce(n, parents)
// </vc-spec>
// <vc-code>
{
    var isSpruce: bool := true;
    for node := 0 to n - 1
        invariant 0 <= node <= n
        invariant isSpruce == (forall k :: 0 <= k < node && hasChildren(k, parents, n) ==> countLeafChildren(k, parents, n) >= 3)
    {
        if hasChildren(node, parents, n) {
            if countLeafChildren(node, parents, n) < 3 {
                isSpruce := false;
            }
        }
    }

    if isSpruce {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

