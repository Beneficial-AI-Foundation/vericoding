//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL
method Postorder(tree: Tree)
{
    match tree {
        case Empty => 
        case Node(left, value, right) =>
            Postorder(left);
            Postorder(right);
            print value, " ";
    }
}