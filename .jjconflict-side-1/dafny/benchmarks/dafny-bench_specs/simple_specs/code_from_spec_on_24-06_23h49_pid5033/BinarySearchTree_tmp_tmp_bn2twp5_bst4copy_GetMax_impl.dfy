//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL GetMax
method GetMax(tree: Tree) returns (res: int)
{
    match tree {
        case Empty => res := 0;
        case Node(left, value, right) => 
            var leftMax := GetMax(left);
            var rightMax := GetMax(right);
            res := value;
            if leftMax > res {
                res := leftMax;
            }
            if rightMax > res {
                res := rightMax;
            }
    }
}