type A; 
type Foo A B; //the A here does not refer to the A above

function f<B>(y: int, x: Foo int B) returns (bool); /* type parameter */

procedure m<B>(x: int, b: B, c: Foo int B) returns () /* type parameter */
{
  var y: Foo A int;
  var z: Foo A B; //B is given by type parameter of procedure 
  assume x > 0; 
  assert x >= 0;
}

procedure m2(z: Foo bool bool) returns ()
{
    var h: Foo int int;
    // assert h == z;    /*type error: h and z do not have the same type*/
    
    call m(0, 0, h);
}

procedure m3() returns ()
{
  assume (forall <B> x: int, y: Foo int B :: x > 0 ==> f(x, y));
}

var m : <C,B> [Foo C B] C;