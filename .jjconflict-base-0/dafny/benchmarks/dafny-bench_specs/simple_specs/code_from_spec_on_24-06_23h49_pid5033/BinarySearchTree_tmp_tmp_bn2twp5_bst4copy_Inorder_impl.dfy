//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL 
method Inorder(tree: Tree)
{
    match tree
    case Empty =>
    case Node(left, value, right) =>
        Inorder(left);
        Inorder(right);
}