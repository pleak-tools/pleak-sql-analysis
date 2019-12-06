Select count(*) 
from satellites
where
  (satellites.xx ^ 2 + 
  satellites.yy ^ 2 +
  satellites.zz ^ 2)^0.5 < 6000;
