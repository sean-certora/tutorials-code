
methods {
    function balanceOf(address)              external returns(uint256) envfree;
    function allowance(address,address)      external returns(uint256) envfree;
    function totalSupply()                   external returns(uint256) envfree;
    function totalAssets()                   external returns(uint256) envfree;
    function convertToShares(uint256 assets) external returns(uint256) envfree;
    function convertToAssets(uint256 shares) external returns(uint256) envfree;
    function previewDeposit(uint256 assets)  external returns(uint256) envfree;
    function previewMint(uint256 shares)     external returns(uint256) envfree;
    function previewWithdraw(uint256 assets) external returns(uint256) envfree;
    function previewRedeem(uint256 shares)   external returns(uint256) envfree;
}


/*
 * Partial sums for the ERC4626 token balance
 */

// Partial sum of balances.
//   sumOfBalances[x] = \sum_{i=0}^{x-1} balances[i];
ghost mapping(mathint => mathint) sumOfBalances {
    init_state axiom forall mathint addr. sumOfBalances[addr] == 0;
}

// ghost copy of balanceOf
ghost mapping(address => uint256) ghost_balanceOf {
    init_state axiom forall address addr. ghost_balanceOf[addr] == 0;
}

hook Sload uint256 b balanceOf[KEY address addr] {
    require(ghost_balanceOf[addr] == b, "Ghost balance and balance must always remain synced");
}

/*
 *   The havoc here is a bit dangerous because this is not proved
 */
hook Sstore balanceOf[KEY address addr] uint256 b_1 (uint256 b_0) {
    havoc sumOfBalances assuming
      forall mathint x. sumOfBalances@new[x] ==
          sumOfBalances@old[x] + (to_mathint(addr) < x ? b_1 - b_0 : 0);
    ghost_balanceOf[addr] = b_1;
}

invariant sumOfBalancesStartsAtZero()
    sumOfBalances[0] == 0;

invariant sumOfBalancesGrowsCorrectly()
    forall address addr. sumOfBalances[to_mathint(addr) + 1] ==
        sumOfBalances[to_mathint(addr)] + ghost_balanceOf[addr];

invariant sumOfBalancesMonotone()
    forall mathint i. forall mathint j. (i <= j) => (sumOfBalances[i] <= sumOfBalances[j])
    {
        preserved {
            requireInvariant sumOfBalancesStartsAtZero();
            requireInvariant sumOfBalancesGrowsCorrectly();
        }
    }

invariant sumOfBalancesEqualsTotalSupply()
    sumOfBalances[2^160] == to_mathint(totalSupply())
    {
        preserved {
            requireInvariant sumOfBalancesStartsAtZero();
            requireInvariant sumOfBalancesGrowsCorrectly();
            requireInvariant sumOfBalancesMonotone();
        }
    }

/*
 * Partial sums for the underlying token `asset`
 */

/* So far I'm just going to copy these. I wonder if it can be parameterised somehow */



/**************************************************************************/

function safeAssumptions() {
    requireInvariant sumOfBalancesStartsAtZero();
    requireInvariant sumOfBalancesGrowsCorrectly();
    requireInvariant sumOfBalancesMonotone();
    requireInvariant sumOfBalancesEqualsTotalSupply();
}

invariant sumOfTwoBalancesCannotExceedTotalSupply(address addr1, address addr2)
    addr1 != addr2 => ghost_balanceOf[addr1] + ghost_balanceOf[addr2] <= totalSupply()
    {
        preserved {
            safeAssumptions();
        }
    }

rule sumOfTwoBalancesCannotExceedTotalSupply2(address addr1, address addr2, env e, method f, calldataarg args)
filtered { f -> !f.isView }
{
    safeAssumptions();
    f(e, args);
    assert addr1 != addr2 => ghost_balanceOf[addr1] + ghost_balanceOf[addr2] <= totalSupply();
}
