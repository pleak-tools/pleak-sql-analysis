SELECT
(cat.gender exact AND cat.color exact) OR (cat.gender exact AND cat.color exact)
FROM cat WHERE available;
