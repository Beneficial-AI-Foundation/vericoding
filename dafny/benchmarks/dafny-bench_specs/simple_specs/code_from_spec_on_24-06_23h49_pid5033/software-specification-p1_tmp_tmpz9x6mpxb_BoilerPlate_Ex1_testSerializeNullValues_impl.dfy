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


//IMPL testSerializeNullValues
method testSerializeNullValues()
{
    var leaf := Leaf(0);
    var result := serialise(leaf);
    
    var singleNode := SingleNode(0, Leaf(0));
    var result2 := serialise(singleNode);
    
    var doubleNode := DoubleNode(0, Leaf(0), Leaf(0));
    var result3 := serialise(doubleNode);
}