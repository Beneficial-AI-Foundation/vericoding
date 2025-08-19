//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL 
method Postorder(tree: Tree)
{
    match tree {
        case Empty => 
            // Do nothing for empty tree
        case Node(left, value, right) =>
            // Visit left subtree
            Postorder(left);
            // Visit right subtree  
            Postorder(right);
            // Process current node (in a real implementation, 
            // this might print the value or add it to a result)
    }
}