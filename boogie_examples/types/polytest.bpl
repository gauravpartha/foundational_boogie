type Foo A B; //the A here does not refer to the A above

//function f<X,Y>(a: Foo X Y) : returns (Y); // does not compile, why?
function f<X,Y>(a: Foo X Y) : (Y); // compiles

procedure m<B>(x: int, b: B, c: Foo int B) returns () /* type parameter */
{
  var y: Foo bool int;
  var z: Foo bool B; //B is given by type parameter of procedure 
  assume f(y) > 0;
  assert f(y) >= 0;
}