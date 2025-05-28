newtype int8 = x | -0x80 <= x < 0x80
newtype int16 = x: int | -128 <= x < 128
newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000
class Material
  {
  var name: string
  var quantity: int32
  constructor CONSTRUCTOR_1_PARAM( name: string)
    decreases *
  {
    //Default Member Variable Values Here
    this.quantity := 0 ;

    {
      this.name := name;
    }
  }
  constructor CONSTRUCTOR_2_PARAM( name: string,quantity: int32)
    decreases *
  {
    //Default Member Variable Values Here
    this.quantity := 0 ;

    {
      this.name := name;
      this.quantity := quantity;
    }
  }
}
class Bom
  {
  var bomData: map<string, seq<Material>>
  method addProduct( productName: string,materials: seq<Material>)
    decreases *
    modifies this
  {
    bomData := bomData[ productName := materials ];
  }
  method getMaterialsForProduct( productName: string) returns ( RES__: seq<Material> )
    decreases *
    modifies this
  {
    if(!(productName in bomData))
    {
      return [];
    }
    return bomData[productName];
  }
}
