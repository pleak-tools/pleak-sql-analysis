insert into wish_summary select
    wishes.item_id AS item_id,
    SUM(wishes.quantity) AS need
from wishes
group by wishes.item_id;

insert into missing_items
select items.item_id as item_id, 
	items.itemname as itemname, 
	items.color as color, 
	(ws.need - items.quantity) as needcount
from items, wish_summary  AS ws
where
ws.item_id = items.item_id
and items.quantity < ws.need;

insert into res
SELECT SUM(missing_items.needcount)
from missing_items
where missing_items.color='brown';
