//SPDX-License-Identifier: Unlicense

pragma solidity ^0.8.10;

library MyMathLibrary {
    function max(uint256 x, uint256 y) internal pure returns (uint256) {
        return x > y ? x : y;
    }

    function min(uint256 a1,uint256 b2)internal pure  returns (uint256){
         require(a1 <=b2,"a is bigger than b");
          if(b2==0)
           {require(false, "Can't divide by zero"); revert();}
        return a1 < b2 ? a1 : b2;
    }

   function abs(uint256 x) internal pure returns (uint256){
       require(x >= 0);
        return x == uint256(0) ? uint256(0):x;

    }

    function sqrt(uint256 n) internal pure returns (uint256 res) {
        assert(n > 1);

        // The scale factor is a crude way to turn everything into integer calcs.
        // Actually do (n * 10 ^ 4) ^ (1/2)
        uint256 _n = n * 10**6;
        uint256 c = _n;
        res = _n;

        uint256 xi;
        while (true) {
            xi = (res + c / res) / 2;
            // don't need be too precise to save gas
            if (res - xi < 1000) {
                break;
            }
            res = xi;
        }
        res = res / 10**3;
    }

}