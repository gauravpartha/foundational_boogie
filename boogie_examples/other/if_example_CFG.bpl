implementation p()
{
  var x: int;


  anon0:
    havoc x;
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} 5 >= x;
    x := 1;
    goto anon3;

  anon3:
    assert x > 0;
    return;

  anon4_Then:
    assume {:partition} x > 5;
    x := 10;
    goto anon3;
}
