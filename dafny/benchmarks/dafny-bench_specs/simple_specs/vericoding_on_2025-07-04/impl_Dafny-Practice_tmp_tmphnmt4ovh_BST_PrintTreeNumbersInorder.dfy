//ATOM
datatype Tree = Empty | Node(int,Tree,Tree)

//IMPL 
method PrintTreeNumbersInorder(t: Tree)
{
    match t {
        case Empty => 
        case Node(value, left, right) =>
            PrintTreeNumbersInorder(left);
            print value;
            PrintTreeNumbersInorder(right);
    }
}