//ATOM
datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)


//ATOM

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)


//ATOM

function serialise<V>(t : Tree<V>) : seq<Code<V>> 
{
 match t {
  case Leaf(v) => [ CLf(v) ]
  case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
  case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
 }
}


//IMPL 

method testSerializeNullValues()
{
    // Test with simple leaf nodes
    var leaf1 := Leaf(0);
    var result1 := serialise(leaf1);
    
    // Test with single node
    var single1 := SingleNode(1, Leaf(2));
    var result2 := serialise(single1);
    
    // Test with double node
    var double1 := DoubleNode(3, Leaf(4), Leaf(5));
    var result3 := serialise(double1);
    
    // Test with more complex tree
    var complex := DoubleNode(6, SingleNode(7, Leaf(8)), Leaf(9));
    var result4 := serialise(complex);
}