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
lemma CountLeafChildrenNonNegative(node: int, parents: seq<int>, n: int)
    requires ValidInput(n, parents)
    requires 0 <= node < n
    ensures countLeafChildren(node, parents, n) >= 0
{
}

lemma HasChildrenImpliesValidChild(node: int, parents: seq<int>, n: int)
    requires ValidInput(n, parents)
    requires 0 <= node < n
    requires hasChildren(node, parents, n)
    ensures exists i :: 0 <= i < n-1 && parents[i] - 1 == node
{
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
    var node := 0;
    while (node < n)
        invariant 0 <= node <= n
        invariant forall k :: 0 <= k < node && hasChildren(k, parents, n) ==> 
            countLeafChildren(k, parents, n) >= 3
    {
        if (hasChildren(node, parents, n)) {
            var leafCount := countLeafChildren(node, parents, n);
            if (leafCount < 3) {
                return "No";
            }
        }
        node := node + 1;
    }
    return "Yes";
}
// </vc-code>

