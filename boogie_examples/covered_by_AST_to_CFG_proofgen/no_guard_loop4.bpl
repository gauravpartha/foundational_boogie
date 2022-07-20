procedure  M();

implementation M()
{
    var x: int;
    var y: int;
    var z: int;

    havoc x;
    havoc y;
    havoc z;

    while (*)
    {
        x := x + y + z;
        
        while (y > 10)
        {
            x := x*10;
        }

        if(x-10 > 200)
        {
            y := z+7;
        }
    }
}