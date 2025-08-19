//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL 
method GetMin(tree: Tree) returns (res: int)
{
    match tree {
        case Empty => res := 0;
        case Node(left, value, right) => {
            var leftMin := GetMin(left);
            var rightMin := GetMin(right);
            res := value;
            if left != Empty && leftMin < res {
                res := leftMin;
            }
            if right != Empty && rightMin < res {
                res := rightMin;
            }
        }
    }
}