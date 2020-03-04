procedure desugar1() returns ()
{
    var x: int;
    var y: int;
    var z: int;

    x,y := z+4, z*10;

    if(z > 0) {
        havoc x,y;
    } else {
        havoc z;
    }

}