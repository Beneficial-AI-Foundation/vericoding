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
    // Test with a simple leaf
    var leaf := Leaf(42);
    var leafSerialized := serialise(leaf);
    
    // Test with a single node
    var singleNode := SingleNode(10, Leaf(5));
    var singleNodeSerialized := serialise(singleNode);
    
    // Test with a double node
    var doubleNode := DoubleNode(20, Leaf(15), Leaf(25));
    var doubleNodeSerialized := serialise(doubleNode);
    
    // More complex tree
    var complexTree := DoubleNode(1, SingleNode(2, Leaf(3)), DoubleNode(4, Leaf(5), Leaf(6)));
    var complexSerialized := serialise(complexTree);
}