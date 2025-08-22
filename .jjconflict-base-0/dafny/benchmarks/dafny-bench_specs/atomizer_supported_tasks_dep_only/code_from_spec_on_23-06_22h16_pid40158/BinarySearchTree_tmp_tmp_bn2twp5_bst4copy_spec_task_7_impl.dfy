//ATOM Tree
datatype Tree = Node(data: int, left: Tree?, right: Tree?) | Empty

//ATOM BinarySearchTree

//ATOM maxValue

//ATOM minValue

//ATOM GetMin

//ATOM GetMax

//ATOM insert

//ATOM insertRecursion

//ATOM delete

//ATOM Inorder

// IMPL Postorder
/* code modified by LLM (iteration 4): Fixed null checks by properly matching Tree? variants - use recursive calls on Some(subtree) and match against None instead of null */
method Postorder(tree: Tree)
    decreases tree
{
    match tree {
        case Node(data, left, right) => 
            if left.Some? {
                Postorder(left.value);
            }
            if right.Some? {
                Postorder(right.value);
            }
            print data;
        case Empty =>
    }
}

//ATOM Main