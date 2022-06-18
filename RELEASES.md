# 0.0.7

- Added feature for optional serde support.

- Added doc_cfg to docs.rs build.

# 0.0.6

- Fixed incorrect integer formatting across most implemented fmt traits (Debug is fine and unchanged).

- Fixed the sign of a remainder in a truncated division (earlier matched the sign of a quotient, now matches the sign of a dividend).

- Added `unsigned_abs` and euclidean division for signed integers. 

# 0.0.5

First unstable release.