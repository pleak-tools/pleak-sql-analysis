SELECT COUNT(*)
FROM person,
     community,
     person2diseasestate
WHERE community.community_id = person.residence
AND person2diseasestate.person_id = person.person_id
AND person2diseasestate.diseasestate = 'I'
AND community.community_name = 'Cebu City'
;
