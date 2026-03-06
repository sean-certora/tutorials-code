using ERC20Concrete as erc20;

methods {
    function balanceOf(address)               external returns(uint256) envfree;
    function allowance(address,address)       external returns(uint256) envfree;
    function totalSupply()                    external returns(uint256) envfree;
    function totalAssets()                    external returns(uint256) envfree;
    function convertToShares(uint256 assets)  external returns(uint256) envfree;
    function convertToAssets(uint256 shares)  external returns(uint256) envfree;
    function previewDeposit(uint256 assets)   external returns(uint256) envfree;
    function previewMint(uint256 shares)      external returns(uint256) envfree;
    function previewWithdraw(uint256 assets)  external returns(uint256) envfree;
    function previewRedeem(uint256 shares)    external returns(uint256) envfree;

    /* non env-free */
    function deposit(uint256 assets,address receiver)  external returns(uint256);

    /* ERC20 methods */
    function erc20.balanceOf(address)         external returns(uint256) envfree;
    function erc20.totalSupply()              external returns(uint256) envfree;
    function erc20.allowance(address,address) external returns(uint256) envfree;
}

// ghost mapping(mathint => mathint) sumOfAssetBalances {
//     init_state axiom forall mathint addr. sumOfAssetBalances[addr] == 0;
// }

// hook Sload uint256 b erc20.balanceOf[KEY address addr] {
//     require(ghost_assetBalanceOf[addr] == b, "Ghost balance and balance must always remain synced");
// }



/*
 * Partial sums for the ERC4626 vault token balances
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

/* "minting shares is monotonic" */
invariant sumOfBalancesMonotone()
    forall mathint i. forall mathint j. (i <= j) => (sumOfBalances[i] <= sumOfBalances[j])
    {
        preserved {
            requireInvariant sumOfBalancesStartsAtZero();
            requireInvariant sumOfBalancesGrowsCorrectly();
        }
    }

/* "Total supply of the vault is the sum of its balances" */
invariant sumOfBalancesEqualsTotalSupply()
    sumOfBalances[2^160] == to_mathint(totalSupply())
    {
        preserved {
            requireInvariant sumOfBalancesStartsAtZero();
            requireInvariant sumOfBalancesGrowsCorrectly();
            requireInvariant sumOfBalancesMonotone();
        }
    }

/*******************************************************************************************/


/*
 * Here I used ghosts to _constrain_ the allowable havoced state of currentContract.asset
 */

ghost mapping(address => uint256) ghost_assetBalanceOf;

ghost uint256 ghost_assetTotalSupply {
    /* WARNING: Unproved but should be true for any ERC20 token */
    axiom ghost_assetTotalSupply == (usum address a. ghost_assetBalanceOf[a]);
}

hook Sload uint256 b erc20.balanceOf[KEY address addr] {
    if (erc20 == currentContract.asset) {
        require(ghost_assetBalanceOf[addr] == b, "assetBalanceOf must always remain synced");
    }
}

hook Sload uint256 s erc20.totalSupply {
    if (erc20 == currentContract.asset) {
        require(ghost_assetTotalSupply == s, "assetTotalSupply must always remain synced");
    }
}

hook Sstore erc20.totalSupply uint256 s1 (uint256 s0) {
    if (erc20 == currentContract.asset) {
        ghost_assetTotalSupply = s1;
    }
}

hook Sstore erc20.balanceOf[KEY address addr] uint256 b1 (uint256 b0) {
    if (erc20 == currentContract.asset) {
        ghost_assetBalanceOf[addr] = b1;
    }
}

function totalSupplyLessThanTotalAssetsPreserved(env e) {
}

/* This makes it impossible for a user to erc20.transferFrom on the ERC4626 contract's behalf */
invariant noAllowanceForContractOnAsset(address addr)
    erc20.allowance(currentContract, addr) == 0 {
        preserved constructor() {
            require erc20.allowance(currentContract, addr) == 0, "asset should have no allowance for currentContract";
        }
        preserved with(env e) {
            require e.msg.sender != currentContract;
        }
    }


/* "sum of shares cannot exceed the vault's total assets" */
invariant totalSupplyLessThanTotalAssets()
    totalSupply() <= totalAssets()
    {
        preserved with (env e) {
            require e.msg.sender != currentContract; /* FIXME: Still need to prove this */
            requireInvariant noAllowanceForContractOnAsset(e.msg.sender);
            requireInvariant sumOfBalancesStartsAtZero();
            requireInvariant sumOfBalancesGrowsCorrectly();
            requireInvariant sumOfBalancesMonotone();
            requireInvariant sumOfBalancesEqualsTotalSupply();
        }
    }

/* Redundant */
invariant sumOfBalancesLessThanEqualTotalAssets()
    sumOfBalances[2^160] <= totalAssets()
    {
        preserved with (env e) {
            safeAssumptions(e);
            requireInvariant totalSupplyLessThanTotalAssets();
        }
    }

ghost bool noDeposits {
    init_state axiom noDeposits;
}

hook CALL(uint g, address addr, uint value, uint argsOffs, uint argLength, uint retOffset, uint retLength) uint rc {
    if(selector == sig:deposit(uint256, address).selector) {
        require !noDeposits;
    }
}

/* "No assets deposited means no shares are minted and vice versa" */
invariant noDepositsIffNoShares()
    noDeposits <=> totalSupply() == 0
    {
        preserved with (env e) {
            safeAssumptions(e);
        }
    }

/* "minting shares is monotonic" */
// invariant shareMonotonicity
    /* i < j => f(i) <= f(j) */




function safeAssumptions(env e) {
    require e.msg.sender != currentContract; /* FIXME: still need to prove this! */
    requireInvariant noAllowanceForContractOnAsset(e.msg.sender);
    requireInvariant sumOfBalancesStartsAtZero();
    requireInvariant sumOfBalancesGrowsCorrectly();
    requireInvariant sumOfBalancesMonotone();
    requireInvariant sumOfBalancesEqualsTotalSupply();
}

/* Just a fun rule I wrote */
rule assetsCanExistWithZeroTotalAssetsExceptAfterDeposit(method f, env e, calldataarg args) {
    require f.selector == sig:deposit(uint256, address).selector;
    f(e, args);
    satisfy erc20.balanceOf(currentContract) > 0 && totalSupply() == 0;
}

rule sumOfTwoBalancesCannotExceedTotalSupply(address addr1, address addr2, env e, method f, calldataarg args)
filtered { f -> !f.isView }
{
    safeAssumptions(e);
    f(e, args);
    assert addr1 != addr2 => ghost_balanceOf[addr1] + ghost_balanceOf[addr2] <= totalSupply();
}