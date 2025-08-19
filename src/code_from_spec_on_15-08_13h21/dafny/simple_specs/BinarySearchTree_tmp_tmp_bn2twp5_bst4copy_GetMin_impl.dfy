//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL 
method GetMin(tree: Tree) returns (res: int)
{
    match tree {
        case Empty => 
            res := 0; // Default value for empty tree
        case Node(left, value, right) =>
            var leftMin := value;
            var rightMin := value;
            
            if left != Empty {
                leftMin := GetMin(left);
            }
            
            if right != Empty {
                rightMin := GetMin(right);
            }
            
            res := value;
            if leftMin < res {
                res := leftMin;
            }
            if rightMin < res {
                res := rightMin;
            }
    }
}