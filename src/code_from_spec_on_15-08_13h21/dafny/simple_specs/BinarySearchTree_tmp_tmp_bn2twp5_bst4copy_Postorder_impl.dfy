datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL 
method Postorder(tree: Tree)
{
    match tree {
        case Empty => 
            // Do nothing for empty tree
        case Node(left, value, right) =>
            Postorder(left);
            Postorder(right);
            // Process current node value (in actual use, this might print or collect the value)
    }
}