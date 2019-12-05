SELECT person2diseasestate.diseasestate AS ds, COUNT(*)
FROM person,
     community,
     person2diseasestate
WHERE community.community_id = person.residence
AND person2diseasestate.person_id = person.person_id
AND community.community_name = 'Cebu City'
GROUP BY person2diseasestate.diseasestate
;
