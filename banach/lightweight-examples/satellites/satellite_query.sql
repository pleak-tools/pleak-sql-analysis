Select count(*) 
from satellites
where
  floor((satellites.xx ^ 2 + 
  satellites.yy ^ 2 +
  satellites.zz ^ 2)^0.5) < 6000;
