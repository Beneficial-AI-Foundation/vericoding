//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL 
method GetMax(tree: Tree) returns (res: int)
{
    match tree {
        case Empty => 
            res := 0; // Default value for empty tree
        case Node(left, value, right) =>
            if left == Empty && right == Empty {
                res := value;
            } else if left == Empty {
                var rightMax := GetMax(right);
                res := if value > rightMax then value else rightMax;
            } else if right == Empty {
                var leftMax := GetMax(left);
                res := if value > leftMax then value else leftMax;
            } else {
                var leftMax := GetMax(left);
                var rightMax := GetMax(right);
                var maxChild := if leftMax > rightMax then leftMax else rightMax;
                res := if value > maxChild then value else maxChild;
            }
    }
}