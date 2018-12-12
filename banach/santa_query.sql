insert into wish_summary select
    wishes.item_id AS groupid,
    count(*) AS need
from wishes
group by wishes.item_id;

insert into missing_items
select items.item_id as item_id, 
	items.itemname as itemname, 
	items.color as color, 
	(wish_summary.need - items.quantity) as needcount
from items, wish_summary 
where
wish_summary.groupid = items.item_id
and items.quantity < wish_summary.need;

SELECT count(*)
from missing_items
where missing_items.color='brown';
