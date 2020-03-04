/*
procedure var_scope(x:int) returns()
{
    var y: int;
    {
        var z: int;
    }
}
*/


procedure F(n: int) returns (r: int)
{
  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} n <= 100;
    call r := F(n + 11);
    {
      var call0formal#AT#n: int;
      var call1formal#AT#r: int;
      call0formal#AT#n := n + 11;
      havoc call1formal#AT#r;
      assume 100 < call0formal#AT#n ==> call1formal#AT#r == call0formal#AT#n - 10;
      assume call0formal#AT#n <= 100 ==> call1formal#AT#r == 91;
      r := call1formal#AT#r;
    }
    {
      var call0formal#AT#n: int;
      var call1formal#AT#r: int;
      call0formal#AT#n := r;
      havoc call1formal#AT#r;
      assume 100 < call0formal#AT#n ==> call1formal#AT#r == call0formal#AT#n - 10;
      assume call0formal#AT#n <= 100 ==> call1formal#AT#r == 91;
      r := call1formal#AT#r;
    }
    return;

  anon3_Then:
    assume {:partition} 100 < n;
    r := n - 10;
    return;
}