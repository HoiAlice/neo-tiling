# Data for the perturbation tests

Two sources of annual (price vector, output) observations, used by `perturbation/datasets.py`.

## Berndt–Wood KLEM, US manufacturing 1947–1971

`berndt_wood_klem.dat`, 25 rows: year, quantity and price index of gross output (QY, PY),
and quantity and price index of capital (QK, PK), labour (QL, PL), energy (QE, PE) and
non-energy materials (QM, PM), plus other series described in `berndt_wood_klem.txt`.
Reformatted version of the KLEM data set from E. R. Berndt, *The Practice of Econometrics*
(Addison-Wesley, 1991), courtesy of E. R. Berndt; downloaded from
<https://mail.aronaldg.org/webfiles/data/klem.dat>. Original paper: Berndt and Wood (1975),
*Review of Economics and Statistics* 57, 259–268.

Prices: `(PK, PL, PE, PM)`, output: `QY`. Dimension 4, 25 periods.

## EU KLEMS & INTANProd, 2023 release

`euklems.csv` is extracted by `extract_euklems.py` from the full "statistical module" files
of the 2023 release (Luiss Lab of Economics and Energy Transition, Rome),
<https://euklems-intanprod-llee.luiss.it/download/>:

- national accounts: `https://www.dropbox.com/s/nkz7mdp0onken1j/national%20accounts.csv?dl=1`
- capital accounts: `https://www.dropbox.com/s/sp2p4m86et66nfg/capital%20accounts.csv?dl=1`
- variable list: `https://www.dropbox.com/s/srsn4zdb1wta27t/Variable-List-2023.xlsx?dl=1`

Download them into `raw/` (git-ignored, about 80 MB) and run the script. Kept slices:
UK, US, DE, FR, JP; industries TOT, C, F, G, H, J, K, M-N; years 1995–2021.

Per (geo, industry, year): `GO_CP`, `GO_PYP`, `GO_Q` (gross output at current prices, at
previous-year prices, volume), the same for intermediate inputs `II_*`, value added `VA_CP`,
compensation of employees `COMP`, hours worked `H_EMP`, and the capital stock `K_GFCF`
(nominal) and `Kq_GFCF` (volume). The 2023 release has no energy/materials/services split of
intermediate inputs, so the dimension is 3: capital, labour, intermediates.

Derived in `datasets.py`: volumes are chain-linked from `*_PYP` when `*_Q` is missing
(the UK file has no price indices), price of capital `(VA_CP - COMP) / Kq_GFCF`, price of
labour `COMP / H_EMP`, price of intermediates `II_CP / II_Q`, output `GO_Q`.
