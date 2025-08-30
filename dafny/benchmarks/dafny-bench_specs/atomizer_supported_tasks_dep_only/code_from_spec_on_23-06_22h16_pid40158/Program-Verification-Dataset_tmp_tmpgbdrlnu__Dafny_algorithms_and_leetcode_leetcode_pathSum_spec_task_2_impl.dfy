//https://leetcode.com/problems/path-sum

//ATOM TreeNode
datatype TreeNode = Null | Node(val: int, left: TreeNode, right: TreeNode)

//ATOM TreeSeq  
function TreeSeq(root: TreeNode): seq<int>
{
    match root
    case Null => []
    case Node(val, left, right) => [val] + TreeSeq(left) + TreeSeq(right)
}

//ATOM TreeSet
function TreeSet(root: TreeNode): set<int>
{
    match root
    case Null => {}
    case Node(val, left, right) => {val} + TreeSet(left) + TreeSet(right)
}

//ATOM isPath
predicate isPath(root: TreeNode, path: seq<int>)
{
    match root
    case Null => path == []
    case Node(val, left, right) => 
        if |path| == 0 then false
        else if path[0] == val then
            if left == Null && right == Null then |path| == 1
            else (left != Null && isPath(left, path[1..])) || 
                 (right != Null && isPath(right, path[1..]))
        else false
}

//ATOM pathSum
function pathSum(path: seq<int>): int
{
    if |path| == 0 then 0
    else path[0] + pathSum(path[1..])
}

//ATOM hasPathSum
predicate hasPathSum(root: TreeNode, targetSum: int)
{
    match root
    case Null => false
    case Node(val, left, right) =>
        if left == Null && right == Null then val == targetSum
        else (left != Null && hasPathSum(left, targetSum - val)) ||
             (right != Null && hasPathSum(right, targetSum - val))
}

//IMPL Test
method Test() {
}