//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL 
method GetMin(tree: Tree) returns (res: int)
{
    match tree {
        case Empty => 
            // This case is problematic since we must return an int
            // but there's no minimum in an empty tree
            // Without additional specification, I'll return 0 as a default
            res := 0;
        case Node(left, value, right) =>
            match left {
                case Empty => res := value;
                case Node(_, _, _) => res := GetMin(left);
            }
    }
}