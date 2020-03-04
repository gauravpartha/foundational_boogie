type Foo A B; 

function f(x: Foo int bool) returns (bool); /* type parameter */

procedure m() returns () /* type parameter */
{
  var y: Foo int bool;
  var x: Foo int bool;
  assume f(y);
  assert x == y ==> f(y);
}