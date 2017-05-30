select distinct friends.id, friends.first_name, friends.last_name  from logged_in_users, friends  where logged_in_users.id = friends.id
